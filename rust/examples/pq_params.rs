//! Exact evaluation of the post-quantum bound of Theorem 3.16 for the
//! parameters of Remark 7.28 (Rust port of `checks/pq_params.py`).
//!
//! Run: `cargo run --release --example pq_params`
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive};

fn big(x: u128) -> BigInt { BigInt::from(x) }
fn pow2(e: u32) -> BigInt { BigInt::one() << e }
fn q(n: BigInt, d: BigInt) -> BigRational { BigRational::new(n, d) }
fn log2(x: &BigRational) -> f64 {
    let (n, d) = (x.numer(), x.denom());
    let bits = |b: &BigInt| { let s = b.bits() as i64; let sh = (s - 60).max(0); ((b >> sh).to_f64().unwrap()).log2() + sh as f64 };
    bits(n) - bits(d)
}

fn main() {
    let p: u128 = (1u128 << 64) - (1u128 << 32) + 1;
    let f = big(p).pow(4); // |F|, quartic extension
    let t = pow2(64); // query bound Q
    let sigma = 256u32; // hash output length
    let m_log = 32u32; // M = 2^32
    let kappa = 248u32; // queries
    let beta = 320u32; // challenge bits
    let ell = 30u128;
    let k = big(ell + 1); // rounds
    let lmax = pow2(m_log - 1);
    let (qv, qc, qs) = (pow2(36), pow2(36), pow2(30));
    let rmin = beta.min(kappa * m_log);
    let m1 = pow2(m_log - 1);
    let one = BigInt::one();
    let h = pow2(sigma);

    let eps_fold = q(m1.clone() + 2, one.clone()) * (q(one.clone(), f.clone()) + q(one.clone(), pow2(beta)));
    let eps_q = q(big(5).pow(kappa), big(8).pow(kappa));
    let kr = if eps_fold > eps_q { eps_fold.clone() } else { eps_q.clone() };
    let a = q(big(4), one.clone())
        * (q(big(80) * (&t + &k + 1) * (&t + &k), one.clone()) * &kr
            + q((&t + &k + 1) * &k, pow2(rmin)));
    let b = q(big(32) * &lmax, h.clone());
    let c = q(big(8) * (big(160) * &t * (big(2) * &t + big(1)).pow(2u32) + big(16) * &qs * big(m_log as u128 - 1)), h.clone());
    let t1: BigInt = &t + big(1) + &qv + &k + &qc;
    let d = q(big(4) * big(240) * (&t + 1) * t1.pow(2u32), h.clone());
    let e = q(big(2) * qv.pow(2u32) * big(240) * (&t + 2 + &k + &qv), h.clone());
    let tot = &a + &b + &c + &d + &e;
    for (name, x) in [("eps_fold", &eps_fold), ("(5/8)^kappa", &eps_q), ("A (sr term)", &a),
        ("B (extract)", &b), ("C (offline)", &c), ("D (online)", &d), ("E (com)", &e), ("total", &tot)] {
        println!("{name:14} 2^{:.2}", log2(x));
    }
    assert!(log2(&tot) < -31.8);
}
