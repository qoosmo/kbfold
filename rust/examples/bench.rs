//! Benchmarks of Section 9. Usage:
//!   cargo run --release --example bench -- <mode> [max_m]
//!   cargo run --release --features parallel --example bench -- <mode> [max_m]
//! Modes:
//!   scaling  kernel vs coefficient-form encoding, F_{p^2}, classical parameters (148 queries)
//!   pq       post-quantum parameters: F_{p^4}, 248 queries (Remark 7.28)
//!   salt     cost of salting: salt_len 0 vs 32, m = 20
//!   stop     number of folding rounds, m = 20
//!   rate     rate 1/2, 1/4, 1/8, m = 20
//!   breakdown  where the prover time goes (commit and open phases), m = 20
//!   arity    variables folded between committed words, k = 1 .. 4, m = 20
//! Every mode prints CSV with the machine columns `threads` and `parallel`.
use kbfold::field::{ExtField, Field, Fp, Fp2, Fp4};
use kbfold::merkle::MerkleTree;
use kbfold::pcs::{Basis, Params, commit, open, to_coefficients, verify};
use kbfold::poly::ntt;
use std::time::Instant;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn fp(&mut self) -> Fp {
        Fp::new(self.next())
    }
    fn ext<E: ExtField>(&mut self) -> E {
        let d: Vec<Fp> = (0..E::DEGREE).map(|_| self.fp()).collect();
        E::from_digits(&d)
    }
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1e3
}

fn threads() -> usize {
    std::env::var("RAYON_NUM_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()))
}

fn machine() -> String {
    let t = if cfg!(feature = "parallel") {
        threads()
    } else {
        1
    };
    format!("{t},{}", cfg!(feature = "parallel"))
}

struct Row {
    commit_ms: f64,
    open_ms: f64,
    verify_ms: f64,
    proof_kib: f64,
}

fn reps_for(m: usize) -> usize {
    match m {
        0..=16 => 11,
        17..=20 => 5,
        _ => 3,
    }
}

fn run<E: ExtField>(p: &Params, reps: usize, seed: u64) -> Row {
    let mut rng = Rng(seed);
    let table: Vec<Fp> = (0..1usize << p.m).map(|_| rng.fp()).collect();
    let z: Vec<E> = (0..p.m).map(|_| rng.ext()).collect();
    let mut cm = vec![];
    for _ in 0..reps {
        let t = Instant::now();
        let r = commit(p, &table).unwrap();
        cm.push(ms(t));
        std::hint::black_box(r.0);
    }
    let (root, pd) = commit(p, &table).unwrap();
    let mut op = vec![];
    let mut last = None;
    for _ in 0..reps {
        let t = Instant::now();
        let r = open(p, &pd, &z).unwrap();
        op.push(ms(t));
        last = Some(r);
    }
    let (v, proof) = last.unwrap();
    let mut ve = vec![];
    for _ in 0..21 {
        let t = Instant::now();
        let ok = verify(p, &root, &z, v, &proof);
        ve.push(ms(t));
        assert_eq!(ok, Ok(()));
    }
    Row {
        commit_ms: median(cm),
        open_ms: median(op),
        verify_ms: median(ve),
        proof_kib: proof.to_bytes().len() as f64 / 1024.0,
    }
}

fn header(extra: &str) {
    println!("{extra},threads,parallel,commit_ms,open_ms,prover_ms,verify_ms,proof_kib");
}

fn line(extra: String, r: &Row) {
    println!(
        "{extra},{},{:.2},{:.2},{:.2},{:.3},{:.1}",
        machine(),
        r.commit_ms,
        r.open_ms,
        r.commit_ms + r.open_ms,
        r.verify_ms,
        r.proof_kib
    );
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "scaling".into());
    let max_m: usize = std::env::args()
        .nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(22);
    match mode.as_str() {
        "scaling" => {
            header("basis,m,R,s,queries,field");
            for m in (12..=max_m).step_by(2) {
                for basis in [Basis::Kernel, Basis::Monomial] {
                    let p = Params {
                        basis,
                        ..Params::classical(m)
                    };
                    let r = run::<Fp2>(&p, reps_for(m), 1 + m as u64);
                    line(format!("{basis:?},{m},2,{},{},p^2", p.s, p.queries), &r);
                }
            }
        }
        "pq" => {
            header("basis,m,R,s,queries,field");
            for m in (12..=max_m).step_by(2) {
                let p = Params::post_quantum(m);
                let r = run::<Fp4>(&p, reps_for(m), 2 + m as u64);
                line(format!("Kernel,{m},2,{},{},p^4", p.s, p.queries), &r);
            }
        }
        "salt" => {
            header("m,salt_len");
            let m = max_m.min(20);
            for salt_len in [0, 32] {
                let p = Params {
                    salt_len,
                    ..Params::classical(m)
                };
                let r = run::<Fp2>(&p, 5, 3);
                line(format!("{m},{salt_len}"), &r);
            }
        }
        "stop" => {
            header("m,s,final_len");
            let m = max_m.min(20);
            for s in (8..=m).step_by(2) {
                let p = Params {
                    s,
                    ..Params::classical(m)
                };
                let r = run::<Fp2>(&p, 3, 77);
                line(format!("{m},{s},{}", 1 << (m - s)), &r);
            }
        }
        "rate" => {
            header("m,R,queries");
            let m = max_m.min(20);
            for rr in [1, 2, 3] {
                // queries: smallest kappa with (1 - delta)^kappa < 2^-100, delta = (1 - rho)/2
                let delta = (1.0 - 1.0 / (1u64 << rr) as f64) / 2.0;
                let q = (100.0 / -(1.0 - delta).log2()).ceil() as usize;
                let p = Params {
                    log_inv_rate: rr,
                    queries: q,
                    ..Params::classical(m)
                };
                let r = run::<Fp2>(&p, 3, 99);
                line(format!("{m},{rr},{q}"), &r);
            }
        }
        "arity" => {
            header("m,k,field");
            let m = max_m.min(20);
            for k in 1..=4 {
                let p = Params {
                    fold_log: k,
                    ..Params::classical(m)
                };
                let r = run::<Fp2>(&p, 5, 11);
                line(format!("{m},{k},p^2"), &r);
            }
            for k in [1, 4] {
                let p = Params {
                    fold_log: k,
                    ..Params::post_quantum(m)
                };
                let r = run::<Fp4>(&p, 5, 12);
                line(format!("{m},{k},p^4"), &r);
            }
        }
        "breakdown" => {
            // commit: transform, NTT, Merkle tree; the rest of the open time is the sumcheck,
            // the folds and their trees, and the query phase.
            println!("basis,m,threads,parallel,transform_ms,ntt_ms,merkle_ms,commit_ms,open_ms");
            let m = max_m.min(20);
            for basis in [Basis::Kernel, Basis::Monomial] {
                let p = Params {
                    basis,
                    ..Params::classical(m)
                };
                let mut rng = Rng(5);
                let table: Vec<Fp> = (0..1usize << m).map(|_| rng.fp()).collect();
                let omega = Fp::two_adic_root((m + p.log_inv_rate) as u32);
                let (mut tr, mut nt, mut mk) = (vec![], vec![], vec![]);
                for _ in 0..5 {
                    let t0 = Instant::now();
                    let mut w = table.clone();
                    to_coefficients(p.basis, &mut w);
                    let t1 = Instant::now();
                    w.resize(p.n(), Fp::ZERO);
                    ntt(&mut w, omega);
                    let t2 = Instant::now();
                    let tree =
                        MerkleTree::new_fibres(&w, p.groups()[0].1, &[0u8; 32], b"w0", p.salt_len);
                    std::hint::black_box(tree.root());
                    tr.push((t1 - t0).as_secs_f64() * 1e3);
                    nt.push((t2 - t1).as_secs_f64() * 1e3);
                    mk.push(ms(t2));
                }
                let r = run::<Fp2>(&p, 5, 5);
                println!(
                    "{basis:?},{m},{},{:.2},{:.2},{:.2},{:.2},{:.2}",
                    machine(),
                    median(tr),
                    median(nt),
                    median(mk),
                    r.commit_ms,
                    r.open_ms
                );
            }
        }
        _ => eprintln!("unknown mode {mode}"),
    }
    let _ = Fp2::ONE;
}
