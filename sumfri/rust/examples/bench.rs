//! Benchmarks of Section 8. Usage:
//!   cargo run --release --example bench -- <mode> [max_m]
//! Modes:
//!   sum        the sum sum_a f(a): Sum-FRI (Pi_sum), KBFold (kernel, 2^n f~(1/2,...,1/2)),
//!              coefficient form with a degree-2 sumcheck (KBFold `Basis::Monomial`), and the
//!              quotient opening of V_f at X = 1; F_{p^2}, classical parameters
//!   eval       evaluation at a random point: Sum-FRI (P_f(z)) vs KBFold kernel and
//!              coefficient form (f~(z)); F_{p^2}, classical parameters
//!   pq         `sum` and `eval` for Sum-FRI and KBFold with the post-quantum parameters (F_{p^4},
//!              248 queries)
//!   breakdown  where the time goes, m = 20: NTT and tree of the commitment; open phases
//! Every mode prints CSV; the column `scheme` names the scheme.
use kbfold::field::{ExtField, Field, Fp, Fp2, Fp4};
use kbfold::merkle::MerkleTree;
use kbfold::pcs as kb;
use kbfold::poly::ntt;
use std::time::Instant;
use sumfri::{pcs, quotient};

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

fn reps_for(m: usize) -> usize {
    match m {
        0..=16 => 11,
        17..=20 => 5,
        _ => 3,
    }
}

const VREPS: usize = 21;

struct Row {
    commit_ms: f64,
    open_ms: f64,
    verify_ms: f64,
    proof_kib: f64,
}

fn print(scheme: &str, m: usize, r: &Row) {
    println!(
        "{scheme},{m},{:.2},{:.2},{:.3},{:.1}",
        r.commit_ms, r.open_ms, r.verify_ms, r.proof_kib
    );
}

fn sp(m: usize, pq: bool) -> pcs::Params {
    if pq {
        pcs::Params::post_quantum(m)
    } else {
        pcs::Params::classical(m)
    }
}

fn kp(m: usize, basis: kb::Basis, pq: bool) -> kb::Params {
    let mut p = if pq {
        kb::Params::post_quantum(m)
    } else {
        kb::Params::classical(m)
    };
    p.basis = basis;
    p
}

/// Sum-FRI: `z = None` is Pi_sum, otherwise Pi_eval at a random point.
fn run_sumfri<E: ExtField>(p: &pcs::Params, eval: bool, seed: u64) -> Row {
    let mut rng = Rng(seed);
    let table: Vec<Fp> = (0..1usize << p.m).map(|_| rng.fp()).collect();
    let z: Vec<E> = if eval {
        (0..p.m).map(|_| rng.ext()).collect()
    } else {
        vec![E::ONE; p.m]
    };
    let reps = reps_for(p.m);
    let (mut cm, mut op) = (vec![], vec![]);
    let mut last = None;
    for _ in 0..reps {
        let t = Instant::now();
        let (root, pd) = pcs::commit(p, &table).unwrap();
        cm.push(ms(t));
        let t = Instant::now();
        let (v, proof) = pcs::open(p, &pd, &z).unwrap();
        op.push(ms(t));
        last = Some((root, v, proof));
    }
    let (root, v, proof) = last.unwrap();
    let mut vf = vec![];
    for _ in 0..VREPS {
        let t = Instant::now();
        pcs::verify(p, &root, &z, v, &proof).unwrap();
        vf.push(ms(t));
    }
    Row {
        commit_ms: median(cm),
        open_ms: median(op),
        verify_ms: median(vf),
        proof_kib: proof.size_bytes() as f64 / 1024.0,
    }
}

/// KBFold (kernel or coefficient form): `eval = false` proves the sum as 2^n f~(1/2, ..., 1/2).
fn run_kbfold<E: ExtField>(p: &kb::Params, eval: bool, seed: u64) -> Row {
    let mut rng = Rng(seed);
    let table: Vec<Fp> = (0..1usize << p.m).map(|_| rng.fp()).collect();
    let half = E::from(Fp::new(2).inv());
    let z: Vec<E> = if eval {
        (0..p.m).map(|_| rng.ext()).collect()
    } else {
        vec![half; p.m]
    };
    let reps = reps_for(p.m);
    let (mut cm, mut op) = (vec![], vec![]);
    let mut last = None;
    for _ in 0..reps {
        let t = Instant::now();
        let (root, pd) = kb::commit(p, &table).unwrap();
        cm.push(ms(t));
        let t = Instant::now();
        let (v, proof) = kb::open(p, &pd, &z).unwrap();
        op.push(ms(t));
        last = Some((root, v, proof));
    }
    let (root, v, proof) = last.unwrap();
    if !eval {
        // the sum is 2^n f~(1/2, ..., 1/2)
        let sum = table.iter().fold(Fp::ZERO, |s, &x| s + x);
        assert_eq!(v * Fp::new(2).pow(p.m as u64), E::from(sum));
    }
    let mut vf = vec![];
    for _ in 0..VREPS {
        let t = Instant::now();
        kb::verify(p, &root, &z, v, &proof).unwrap();
        vf.push(ms(t));
    }
    Row {
        commit_ms: median(cm),
        open_ms: median(op),
        verify_ms: median(vf),
        proof_kib: proof.size_bytes() as f64 / 1024.0,
    }
}

fn run_quotient<E: ExtField>(p: &pcs::Params, seed: u64) -> Row {
    let mut rng = Rng(seed);
    let table: Vec<Fp> = (0..1usize << p.m).map(|_| rng.fp()).collect();
    let reps = reps_for(p.m);
    let (mut cm, mut op) = (vec![], vec![]);
    let mut last = None;
    for _ in 0..reps {
        let t = Instant::now();
        let (root, pd) = quotient::commit(p, &table).unwrap();
        cm.push(ms(t));
        let t = Instant::now();
        let (v, proof) = quotient::open::<E>(p, &pd).unwrap();
        op.push(ms(t));
        last = Some((root, v, proof));
    }
    let (root, v, proof) = last.unwrap();
    let mut vf = vec![];
    for _ in 0..VREPS {
        let t = Instant::now();
        quotient::verify(p, &root, v, &proof).unwrap();
        vf.push(ms(t));
    }
    Row {
        commit_ms: median(cm),
        open_ms: median(op),
        verify_ms: median(vf),
        proof_kib: proof.size_bytes() as f64 / 1024.0,
    }
}

fn breakdown(m: usize) {
    let p = pcs::Params::classical(m);
    let mut rng = Rng(1);
    let table: Vec<Fp> = (0..1usize << m).map(|_| rng.fp()).collect();
    let reps = reps_for(m);
    let (mut t_ntt, mut t_tree, mut t_commit, mut t_sum, mut t_eval) =
        (vec![], vec![], vec![], vec![], vec![]);
    let z: Vec<Fp2> = (0..m).map(|_| rng.ext()).collect();
    for _ in 0..reps {
        let t = Instant::now();
        let mut w = table.clone();
        w.resize(p.n(), Fp::ZERO);
        ntt(&mut w, Fp::two_adic_root((p.m + p.log_inv_rate) as u32));
        t_ntt.push(ms(t));
        let t = Instant::now();
        let tree = MerkleTree::new_fibres(&w, p.groups()[0].1, &[7u8; 32], b"w0", p.salt_len);
        t_tree.push(ms(t));
        std::hint::black_box(tree.root());
        let t = Instant::now();
        let (_, pd) = pcs::commit(&p, &table).unwrap();
        t_commit.push(ms(t));
        let t = Instant::now();
        std::hint::black_box(pcs::open_sum::<Fp2>(&p, &pd).unwrap());
        t_sum.push(ms(t));
        let t = Instant::now();
        std::hint::black_box(pcs::open(&p, &pd, &z).unwrap());
        t_eval.push(ms(t));
    }
    println!("phase,m,ms");
    println!("commit_ntt,{m},{:.2}", median(t_ntt));
    println!("commit_tree,{m},{:.2}", median(t_tree));
    println!("commit_total,{m},{:.2}", median(t_commit));
    println!("open_sum,{m},{:.2}", median(t_sum));
    println!("open_eval,{m},{:.2}", median(t_eval));
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(String::as_str).unwrap_or("sum");
    let max: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(22);
    let header = "scheme,m,commit_ms,open_ms,verify_ms,proof_kib";
    match mode {
        "sum" => {
            println!("{header}");
            for m in (12..=max).step_by(2) {
                print("sumfri", m, &run_sumfri::<Fp2>(&sp(m, false), false, m as u64));
                print("kbfold-kernel", m, &run_kbfold::<Fp2>(&kp(m, kb::Basis::Kernel, false), false, m as u64));
                print("coeff-sumcheck", m, &run_kbfold::<Fp2>(&kp(m, kb::Basis::Monomial, false), false, m as u64));
                print("quotient", m, &run_quotient::<Fp2>(&sp(m, false), m as u64));
            }
        }
        "eval" => {
            println!("{header}");
            for m in (12..=max).step_by(2) {
                print("sumfri", m, &run_sumfri::<Fp2>(&sp(m, false), true, m as u64));
                print("kbfold-kernel", m, &run_kbfold::<Fp2>(&kp(m, kb::Basis::Kernel, false), true, m as u64));
                print("coeff-sumcheck", m, &run_kbfold::<Fp2>(&kp(m, kb::Basis::Monomial, false), true, m as u64));
            }
        }
        "pq" => {
            println!("{header}");
            for m in (12..=max).step_by(2) {
                print("sumfri-sum", m, &run_sumfri::<Fp4>(&sp(m, true), false, m as u64));
                print("kbfold-sum", m, &run_kbfold::<Fp4>(&kp(m, kb::Basis::Kernel, true), false, m as u64));
                print("sumfri-eval", m, &run_sumfri::<Fp4>(&sp(m, true), true, m as u64));
                print("kbfold-eval", m, &run_kbfold::<Fp4>(&kp(m, kb::Basis::Kernel, true), true, m as u64));
            }
        }
        "breakdown" => breakdown(max.min(20)),
        _ => eprintln!("unknown mode {mode}"),
    }
}
