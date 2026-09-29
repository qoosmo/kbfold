use kbfold::error::Error;
use kbfold::field::{ExtField, Field, Fp, Fp2, Fp4};
use kbfold::pcs::{Basis, Params, commit, open, verify};
use kbfold::poly::mle_eval;

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

fn setup<E: ExtField>(
    basis: Basis,
    m: usize,
    s: usize,
    r: usize,
    q: usize,
    seed: u64,
) -> (Params, Vec<Fp>, Vec<E>) {
    let mut rng = Rng(seed);
    let p = Params {
        basis,
        m,
        log_inv_rate: r,
        s,
        queries: q,
        salt_len: 32,
        fold_log: 4,
    };
    let table: Vec<Fp> = (0..1 << m).map(|_| rng.fp()).collect();
    let z: Vec<E> = (0..m).map(|_| rng.ext()).collect();
    (p, table, z)
}

fn completeness<E: ExtField>() {
    for m in 1..=9 {
        for s in 0..=m {
            for r in 1..=3 {
                for (basis, k) in [
                    (Basis::Kernel, 1),
                    (Basis::Kernel, 2),
                    (Basis::Kernel, 3),
                    (Basis::Kernel, 4),
                    (Basis::Monomial, 2),
                ] {
                    let (mut p, table, z) =
                        setup::<E>(basis, m, s, r, 8, 1000 + (m * 100 + s * 10 + r) as u64);
                    p.fold_log = k;
                    let (root, pd) = commit(&p, &table).unwrap();
                    let (v, proof) = open(&p, &pd, &z).unwrap();
                    let t: Vec<E> = table.iter().map(|&x| E::from(x)).collect();
                    assert_eq!(v, mle_eval(&t, &z), "value m={m} s={s}");
                    assert_eq!(
                        verify(&p, &root, &z, v, &proof),
                        Ok(()),
                        "{basis:?} m={m} s={s} r={r} k={k}"
                    );
                }
            }
        }
    }
}

#[test]
fn completeness_quadratic() {
    completeness::<Fp2>();
}

#[test]
fn completeness_quartic() {
    completeness::<Fp4>();
}

#[test]
fn unsalted_trees_are_complete() {
    let (mut p, table, z) = setup::<Fp2>(Basis::Kernel, 8, 5, 2, 20, 3);
    p.salt_len = 0;
    let (root, pd) = commit(&p, &table).unwrap();
    let (v, proof) = open(&p, &pd, &z).unwrap();
    assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()));
}

#[test]
fn recommended_parameters() {
    let mut rng = Rng(5);
    let table: Vec<Fp> = (0..1 << 12).map(|_| rng.fp()).collect();
    let p = Params::post_quantum(12);
    let z: Vec<Fp4> = (0..12).map(|_| rng.ext()).collect();
    let (root, pd) = commit(&p, &table).unwrap();
    let (v, proof) = open(&p, &pd, &z).unwrap();
    assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()));
    let p = Params::classical(12);
    let z: Vec<Fp2> = (0..12).map(|_| rng.ext()).collect();
    let (root, pd) = commit(&p, &table).unwrap();
    let (v, proof) = open(&p, &pd, &z).unwrap();
    assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()));
}

#[test]
fn salts_are_fresh() {
    // two commitments to the same table differ, and both open correctly
    let (p, table, z) = setup::<Fp2>(Basis::Kernel, 8, 4, 2, 16, 4);
    let (r1, pd1) = commit(&p, &table).unwrap();
    let (r2, pd2) = commit(&p, &table).unwrap();
    assert_ne!(r1, r2);
    let (v1, pr1) = open(&p, &pd1, &z).unwrap();
    let (v2, pr2) = open(&p, &pd1, &z).unwrap();
    assert_eq!(v1, v2);
    assert_ne!(pr1.round_salts, pr2.round_salts);
    assert_eq!(verify(&p, &r1, &z, v1, &pr2), Ok(()));
    let (v, pr) = open(&p, &pd2, &z).unwrap();
    assert!(verify(&p, &r1, &z, v, &pr).is_err());
}

#[test]
fn rejects_wrong_value_point_and_root() {
    let (p, table, mut z) = setup::<Fp2>(Basis::Kernel, 10, 7, 2, 30, 7);
    let (root, pd) = commit(&p, &table).unwrap();
    let (v, proof) = open(&p, &pd, &z).unwrap();
    assert!(verify(&p, &root, &z, v + Fp2::ONE, &proof).is_err());
    let mut bad_root = root;
    bad_root[0] ^= 1;
    assert!(verify(&p, &bad_root, &z, v, &proof).is_err());
    z[3] = z[3] + Fp2::ONE;
    assert!(verify(&p, &root, &z, v, &proof).is_err());
}

/// Opening a different table against the committed root must fail.
#[test]
fn rejects_opening_of_other_table() {
    let (p, table, z) = setup::<Fp2>(Basis::Kernel, 8, 5, 2, 40, 11);
    let (root, _pd) = commit(&p, &table).unwrap();
    let mut t2 = table.clone();
    t2[0] = t2[0] + Fp::ONE;
    let (_root2, pd2) = commit(&p, &t2).unwrap();
    let (v2, proof2) = open(&p, &pd2, &z).unwrap();
    assert!(verify(&p, &root, &z, v2, &proof2).is_err());
}

#[test]
fn invalid_parameters_and_inputs() {
    let (p, table, z) = setup::<Fp2>(Basis::Kernel, 6, 3, 2, 8, 12);
    for bad in [
        Params { m: 0, ..p },
        Params {
            log_inv_rate: 0,
            ..p
        },
        Params { m: 31, ..p },
        Params { s: 7, ..p },
        Params { queries: 0, ..p },
        Params { salt_len: 65, ..p },
        Params { fold_log: 0, ..p },
        Params { fold_log: 7, ..p },
    ] {
        assert!(matches!(bad.validate(), Err(Error::Params(_))));
        assert!(matches!(commit(&bad, &table), Err(Error::Params(_))));
    }
    assert!(matches!(commit(&p, &table[1..]), Err(Error::Input(_))));
    let (root, pd) = commit(&p, &table).unwrap();
    assert!(matches!(open(&p, &pd, &z[1..]), Err(Error::Input(_))));
    let (v, proof) = open(&p, &pd, &z).unwrap();
    assert!(matches!(
        verify(&p, &root, &z[1..], v, &proof),
        Err(Error::Input(_))
    ));
    // the verifier with other parameters rejects without panicking
    for other in [
        Params { s: 2, ..p },
        Params { queries: 9, ..p },
        Params { salt_len: 16, ..p },
        Params { s: 6, ..p },
        Params { fold_log: 2, ..p },
    ] {
        assert!(verify(&other, &root, &z, v, &proof).is_err());
    }
}
