use kbfold::field::{Field, Fp, Fp2};
use kbfold::pcs::{commit, open, verify, Basis, Params};
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
    fn fp2(&mut self) -> Fp2 {
        Fp2(self.fp(), self.fp())
    }
}

fn setup(m: usize, s: usize, r: usize, q: usize, seed: u64) -> (Params, Vec<Fp>, Vec<Fp2>, Rng) {
    setup_b(Basis::Kernel, m, s, r, q, seed)
}

fn setup_b(basis: Basis, m: usize, s: usize, r: usize, q: usize, seed: u64) -> (Params, Vec<Fp>, Vec<Fp2>, Rng) {
    let mut rng = Rng(seed);
    let p = Params { basis, m, log_inv_rate: r, s, queries: q };
    let table: Vec<Fp> = (0..1 << m).map(|_| rng.fp()).collect();
    let z: Vec<Fp2> = (0..m).map(|_| rng.fp2()).collect();
    (p, table, z, rng)
}

#[test]
fn completeness_all_parameters() {
    for m in 1..=10 {
        for s in 0..=m {
            for r in 1..=3 {
                for basis in [Basis::Kernel, Basis::Monomial] {
                    let (p, table, z, _) = setup_b(basis, m, s, r, 8, 1000 + (m * 100 + s * 10 + r) as u64);
                    let (root, pd) = commit(&p, &table);
                    let (v, proof) = open(&p, &pd, &z);
                    let t2: Vec<Fp2> = table.iter().map(|&x| x.into()).collect();
                    assert_eq!(v, mle_eval(&t2, &z), "value m={m} s={s}");
                    assert!(verify(&p, &root, &z, v, &proof), "reject {basis:?} m={m} s={s} r={r}");
                }
            }
        }
    }
}

#[test]
fn rejects_wrong_value() {
    let (p, table, z, _) = setup(10, 7, 2, 30, 7);
    let (root, pd) = commit(&p, &table);
    let (v, proof) = open(&p, &pd, &z);
    assert!(!verify(&p, &root, &z, v + Fp2::ONE, &proof));
}

#[test]
fn rejects_wrong_point_and_root() {
    let (p, table, mut z, _) = setup(10, 10, 2, 30, 8);
    let (root, pd) = commit(&p, &table);
    let (v, proof) = open(&p, &pd, &z);
    let mut bad_root = root;
    bad_root[0] ^= 1;
    assert!(!verify(&p, &bad_root, &z, v, &proof));
    z[3] = z[3] + Fp2::ONE;
    assert!(!verify(&p, &root, &z, v, &proof));
}

#[test]
fn rejects_tampered_messages() {
    let (p, table, z, _) = setup(9, 6, 2, 30, 9);
    let (root, pd) = commit(&p, &table);
    let (v, proof) = open(&p, &pd, &z);
    assert!(verify(&p, &root, &z, v, &proof));
    // sumcheck message
    let mut pr = proof.clone();
    pr.sumcheck[2][2] = pr.sumcheck[2][2] + Fp2::ONE;
    assert!(!verify(&p, &root, &z, v, &pr));
    // final table
    let mut pr = proof.clone();
    pr.g[0] = pr.g[0] + Fp2::ONE;
    assert!(!verify(&p, &root, &z, v, &pr));
    // opened value in a query
    let mut pr = proof.clone();
    pr.queries[5].levels[1].a = pr.queries[5].levels[1].a + Fp2::ONE;
    assert!(!verify(&p, &root, &z, v, &pr));
    // intermediate root
    let mut pr = proof.clone();
    pr.roots[0][5] ^= 0xff;
    assert!(!verify(&p, &root, &z, v, &pr));
}

/// Opening a different table against the committed root must fail.
#[test]
fn rejects_opening_of_other_table() {
    let (p, table, z, _) = setup(8, 5, 2, 40, 11);
    let (root, _pd) = commit(&p, &table);
    let mut t2 = table.clone();
    t2[0] = t2[0] + Fp::ONE;
    let (_root2, pd2) = commit(&p, &t2);
    let (v2, proof2) = open(&p, &pd2, &z);
    assert!(!verify(&p, &root, &z, v2, &proof2));
}
