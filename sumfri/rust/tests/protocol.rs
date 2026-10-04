//! Completeness, the claimed value, rejection of a consistent cheater (Theorem 6.13(2)),
//! tampering, and the restriction dictionary (Theorem 4.6) on random instances.

use kbfold::error::Error;
use kbfold::field::{ExtField, Field, Fp, Fp2, Fp4};
use kbfold::poly::{horner, ntt};
use sumfri::pcs::{
    Params, commit, cpoly_eval, cres, monomial_table, open, open_sum, verify, verify_sum,
};

struct Rng(u64);
impl Rng {
    fn fp(&mut self) -> Fp {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        Fp::new(self.0)
    }
}

fn naive_p<E: ExtField>(f: &[Fp], z: &[E]) -> E {
    // P_f(z) = sum_a f(a) prod_k z_k^{a_k}
    (0..f.len()).fold(E::ZERO, |s, a| {
        let mut m = E::ONE;
        for (k, &zk) in z.iter().enumerate() {
            if (a >> k) & 1 == 1 {
                m = m * zk;
            }
        }
        s + E::from(f[a]) * m
    })
}

fn all_params() -> Vec<Params> {
    let mut out = Vec::new();
    for (m, s, k) in [
        (1, 0, 1),
        (1, 1, 1),
        (3, 0, 4),
        (3, 3, 2),
        (6, 3, 1),
        (6, 6, 4),
        (8, 5, 2),
        (8, 8, 4),
        (10, 6, 3),
        (10, 9, 4),
        (11, 7, 4),
    ] {
        for r in [1, 2, 3] {
            out.push(Params {
                m,
                log_inv_rate: r,
                s,
                queries: 24,
                salt_len: 32,
                fold_log: k,
            });
        }
    }
    out
}

fn complete<E: ExtField>(mk: impl Fn(Fp, Fp) -> E, seed: u64) {
    let mut rng = Rng(seed);
    for p in all_params() {
        let table: Vec<Fp> = (0..1 << p.m).map(|_| rng.fp()).collect();
        let (root, pd) = commit(&p, &table).unwrap();
        // evaluation at a random point
        let z: Vec<E> = (0..p.m).map(|_| mk(rng.fp(), rng.fp())).collect();
        let (v, proof) = open(&p, &pd, &z).unwrap();
        assert_eq!(v, naive_p(&table, &z), "value, {p:?}");
        assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()), "{p:?}");
        // a wrong value with the same proof is rejected
        assert!(verify(&p, &root, &z, v + E::ONE, &proof).is_err());
        // the sum
        let (vs, ps) = open_sum::<E>(&p, &pd).unwrap();
        let sum = table.iter().fold(Fp::ZERO, |s, &x| s + x);
        assert_eq!(vs, E::from(sum));
        assert_eq!(verify_sum(&p, &root, vs, &ps), Ok(()), "sum {p:?}");
        assert!(verify_sum(&p, &root, vs + E::ONE, &ps).is_err());
    }
}

#[test]
fn completeness_fp2() {
    complete(Fp2, 7);
}

#[test]
fn completeness_fp4() {
    complete(|a, b| Fp4(Fp2(a, b), Fp2(b, a)), 11);
}

#[test]
fn tampering_is_rejected() {
    let mut rng = Rng(5);
    let p = Params {
        m: 10,
        log_inv_rate: 2,
        s: 6,
        queries: 30,
        salt_len: 32,
        fold_log: 3,
    };
    let table: Vec<Fp> = (0..1 << p.m).map(|_| rng.fp()).collect();
    let (root, pd) = commit(&p, &table).unwrap();
    let (v, proof) = open_sum::<Fp2>(&p, &pd).unwrap();
    assert_eq!(verify_sum(&p, &root, v, &proof), Ok(()));

    let mut bad = proof.clone();
    bad.rounds[2] = bad.rounds[2] + Fp2::ONE;
    assert!(verify_sum(&p, &root, v, &bad).is_err());

    let mut bad = proof.clone();
    bad.g[0] = bad.g[0] + Fp2::ONE;
    assert!(verify_sum(&p, &root, v, &bad).is_err());

    let mut bad = proof.clone();
    bad.level0.values[0][0] = bad.level0.values[0][0] + Fp::ONE;
    assert_eq!(verify_sum(&p, &root, v, &bad), Err(Error::Merkle));

    let mut bad = proof.clone();
    bad.levels[0].values[0][1] = bad.levels[0].values[0][1] + Fp2::ONE;
    assert_eq!(verify_sum(&p, &root, v, &bad), Err(Error::Merkle));

    let mut bad = proof.clone();
    bad.rounds.pop();
    assert_eq!(verify_sum(&p, &root, v, &bad), Err(Error::Shape));

    let mut bad = proof.clone();
    bad.round_salts[0][0] ^= 1;
    assert!(verify_sum(&p, &root, v, &bad).is_err());

    let mut other = root;
    other[0] ^= 1;
    assert!(verify_sum(&p, &other, v, &proof).is_err());
}

/// Theorem 4.6 and Corollary 4.9 on the codeword: folding Enc(f) with theta_1 .. theta_m gives the
/// constant P_f(theta), and V_f(zeta) = P_f(zeta, zeta^2, ...) (Lemma 4.2).
#[test]
fn restriction_dictionary() {
    let mut rng = Rng(3);
    for m in 1..=8 {
        let f: Vec<Fp> = (0..1 << m).map(|_| rng.fp()).collect();
        let fe: Vec<Fp2> = f.iter().map(|&x| Fp2::from(x)).collect();
        let theta: Vec<Fp2> = (0..m).map(|_| Fp2(rng.fp(), rng.fp())).collect();
        // polynomial side: cres m times
        let mut t = fe.clone();
        for &th in &theta {
            t = cres(&t, th);
        }
        assert_eq!(t[0], cpoly_eval(&fe, &theta));
        assert_eq!(t[0], naive_p(&f, &theta));
        // Kronecker substitution
        let zeta = Fp2(rng.fp(), rng.fp());
        let mut pw = Vec::new();
        let mut x = zeta;
        for _ in 0..m {
            pw.push(x);
            x = x * x;
        }
        assert_eq!(horner(&fe, zeta), naive_p(&f, &pw));
        // the monomial table sums to P_f(z)
        let tau = monomial_table(&theta);
        let s = fe.iter().zip(&tau).fold(Fp2::ZERO, |s, (&a, &b)| s + a * b);
        assert_eq!(s, naive_p(&f, &theta));
        // word side: Enc(f) on a domain of size 4N, folded m times, is the constant P_f(theta)
        let n = 4usize << m;
        let omega = Fp::two_adic_root(n.trailing_zeros());
        let mut w: Vec<Fp> = f.clone();
        w.resize(n, Fp::ZERO);
        ntt(&mut w, omega);
        let mut cur: Vec<Fp2> = w.iter().map(|&x| Fp2::from(x)).collect();
        let inv2 = Fp::new(2).inv();
        for (j, &th) in theta.iter().enumerate() {
            let h = cur.len() / 2;
            let om_j = omega.pow(1 << j);
            cur = (0..h)
                .map(|i| {
                    let x_inv = om_j.pow(i as u64).inv();
                    let (a, b) = (cur[i], cur[i + h]);
                    (a + b) * inv2 + th * ((a - b) * (x_inv * inv2))
                })
                .collect();
        }
        assert!(cur.iter().all(|&y| y == t[0]), "m = {m}");
    }
}

/// Example 4.12 of the paper, over F_17 (plain integer arithmetic mod 17).
#[test]
fn example_f17() {
    let q = 17u64;
    let f = [1u64, 2, 3, 4];
    let pf = |x1: u64, x2: u64| (f[0] + f[1] * x1 + f[2] * x2 + f[3] * x1 * x2) % q;
    let vf = |x: u64| (f[0] + f[1] * x + f[2] * x * x + f[3] * x * x * x) % q;
    assert_eq!(pf(1, 1), 10);
    assert_eq!(vf(1), 10);
    // round 1 at z = (1, 1): h(T) = (f0 + f2) + T (f1 + f3) = 4 + 6T, h(1) = 10
    let h = |t: u64| (4 + 6 * t) % q;
    assert_eq!(h(1), 10);
    // theta_1 = 5: cres_5(f) = (1 + 5*2, 3 + 5*4) = (11, 6), new claim h(5) = 0 = 11 + 6
    let c = [(f[0] + 5 * f[1]) % q, (f[2] + 5 * f[3]) % q];
    assert_eq!(c, [11, 6]);
    assert_eq!(h(5), (c[0] + c[1]) % q);
    // theta_2 = 7: the final constant 11 + 6*7 = 2 = P_f(5, 7)
    assert_eq!((c[0] + 7 * c[1]) % q, 2);
    assert_eq!(pf(5, 7), 2);
    // a prover claiming 11 sends s(T) = 1 + 10T; s = h only at T = 5
    let s = |t: u64| (1 + 10 * t) % q;
    assert_eq!(s(1), 11);
    let agree: Vec<u64> = (0..q).filter(|&t| s(t) == h(t)).collect();
    assert_eq!(agree, vec![5]);
}
