//! Benchmarks for Section 8.  Single-threaded.  Usage:
//!   cargo run --release --example bench -- scaling | stop | rate
use kbfold::field::{Field, Fp, Fp2};
use kbfold::merkle::MerkleTree;
use kbfold::pcs::{commit, open, to_coefficients, verify, Basis, Params};
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
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

/// queries for >= 100 bits with delta = (1 - rho)/2
fn queries_for(log_inv_rate: usize) -> usize {
    let rho = 1.0 / (1u64 << log_inv_rate) as f64;
    let delta = (1.0 - rho) / 2.0;
    (100.0 / -(1.0 - delta).log2()).ceil() as usize
}

struct Row {
    commit_ms: f64,
    transform_ms: f64,
    ntt_ms: f64,
    merkle_ms: f64,
    open_ms: f64,
    verify_ms: f64,
    proof_kib: f64,
}

fn run(p: &Params, reps: usize, seed: u64) -> Row {
    let mut rng = Rng(seed);
    let table: Vec<Fp> = (0..1usize << p.m).map(|_| rng.fp()).collect();
    let z: Vec<Fp2> = (0..p.m).map(|_| Fp2(rng.fp(), rng.fp())).collect();
    let omega = Fp::two_adic_root((p.m + p.log_inv_rate) as u32);

    // commit breakdown (same steps as pcs::commit)
    let (mut tr, mut nt, mut mk, mut cm) = (vec![], vec![], vec![], vec![]);
    for _ in 0..reps {
        let t0 = Instant::now();
        let mut w = table.clone();
        to_coefficients(p.basis, &mut w);
        let t1 = Instant::now();
        w.resize(p.n(), Fp::ZERO);
        ntt(&mut w, omega);
        let t2 = Instant::now();
        let tree = MerkleTree::new(&w);
        let t3 = Instant::now();
        std::hint::black_box(tree.root());
        tr.push((t1 - t0).as_secs_f64() * 1e3);
        nt.push((t2 - t1).as_secs_f64() * 1e3);
        mk.push((t3 - t2).as_secs_f64() * 1e3);
        let t4 = Instant::now();
        let r = commit(p, &table);
        cm.push(t4.elapsed().as_secs_f64() * 1e3);
        std::hint::black_box(r.0);
    }
    let (root, pd) = commit(p, &table);
    let mut op = vec![];
    let mut last = None;
    for _ in 0..reps {
        let t = Instant::now();
        let r = open(p, &pd, &z);
        op.push(t.elapsed().as_secs_f64() * 1e3);
        last = Some(r);
    }
    let (v, proof) = last.unwrap();
    let mut ve = vec![];
    for _ in 0..21 {
        let t = Instant::now();
        let ok = verify(p, &root, &z, v, &proof);
        ve.push(t.elapsed().as_secs_f64() * 1e3);
        assert!(ok);
    }
    Row {
        commit_ms: median(cm),
        transform_ms: median(tr),
        ntt_ms: median(nt),
        merkle_ms: median(mk),
        open_ms: median(op),
        verify_ms: median(ve),
        proof_kib: proof.size_bytes() as f64 / 1024.0,
    }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "scaling".into());
    let _ = Fp2::ONE;
    match mode.as_str() {
        "scaling" => {
            println!("basis,m,R,s,queries,commit_ms,transform_ms,ntt_ms,merkle_ms,open_ms,verify_ms,proof_kib");
            for m in (12..=22).step_by(2) {
                for basis in [Basis::Kernel, Basis::Monomial] {
                    let p = Params { basis, m, log_inv_rate: 2, s: m - 4, queries: queries_for(2) };
                    let reps = if m >= 22 { 3 } else if m >= 20 { 5 } else { 11 };
                    let r = run(&p, reps, 1 + m as u64);
                    println!(
                        "{:?},{},{},{},{},{:.2},{:.2},{:.2},{:.2},{:.2},{:.3},{:.1}",
                        basis, m, 2, p.s, p.queries, r.commit_ms, r.transform_ms, r.ntt_ms, r.merkle_ms, r.open_ms, r.verify_ms, r.proof_kib
                    );
                }
            }
        }
        "stop" => {
            println!("m,s,final_len,open_ms,verify_ms,proof_kib");
            let m = 20;
            for s in [8, 10, 12, 14, 16, 18, 20] {
                let p = Params { basis: Basis::Kernel, m, log_inv_rate: 2, s, queries: queries_for(2) };
                let r = run(&p, 3, 77);
                println!("{},{},{},{:.2},{:.3},{:.1}", m, s, 1 << (m - s), r.open_ms, r.verify_ms, r.proof_kib);
            }
        }
        "rate" => {
            println!("m,R,queries,commit_ms,open_ms,verify_ms,proof_kib");
            let m = 20;
            for rr in [1, 2, 3] {
                let p = Params { basis: Basis::Kernel, m, log_inv_rate: rr, s: m - 4, queries: queries_for(rr) };
                let r = run(&p, 3, 99);
                println!("{},{},{},{:.2},{:.2},{:.3},{:.1}", m, rr, p.queries, r.commit_ms, r.open_ms, r.verify_ms, r.proof_kib);
            }
        }
        _ => eprintln!("unknown mode"),
    }
}
