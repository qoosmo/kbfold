//! Every single mutation of an honest proof is rejected, and the verifier never panics on
//! malformed proofs (wrong lengths, truncated salts and paths, random corruption).

use kbfold::field::{ExtField, Field, Fp, Fp2, Fp4};
use kbfold::pcs::{Params, Proof, commit, open, verify};
use std::panic::{AssertUnwindSafe, catch_unwind};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn fp(&mut self) -> Fp {
        Fp::new(self.next())
    }
    fn ext<E: ExtField>(&mut self) -> E {
        let d: Vec<Fp> = (0..E::DEGREE).map(|_| self.fp()).collect();
        E::from_digits(&d)
    }
}

/// All single mutations of a proof: each changes one value, one byte, or one length.
fn mutations<E: ExtField>(pr: &Proof<E>) -> Vec<(String, Proof<E>)> {
    let mut out = Vec::new();
    let mut add = |name: String, f: &dyn Fn(&mut Proof<E>)| {
        let mut q = pr.clone();
        f(&mut q);
        out.push((name, q));
    };
    for j in 0..pr.sumcheck.len() {
        for k in 0..3 {
            add(format!("sumcheck {j} {k}"), &|q| q.sumcheck[j][k] = q.sumcheck[j][k] + E::ONE);
        }
    }
    for j in 0..pr.roots.len() {
        add(format!("root {j}"), &|q| q.roots[j][7] ^= 1);
    }
    for j in 0..pr.round_salts.len() {
        add(format!("round salt {j}"), &|q| q.round_salts[j][0] ^= 1);
        add(format!("round salt {j} short"), &|q| {
            q.round_salts[j].pop();
        });
        add(format!("round salt {j} long"), &|q| q.round_salts[j].push(0));
    }
    for k in 0..pr.g.len() {
        add(format!("g {k}"), &|q| q.g[k] = q.g[k] + E::ONE);
    }
    add("g short".into(), &|q| {
        q.g.pop();
    });
    add("g long".into(), &|q| q.g.push(E::ZERO));
    add("sumcheck short".into(), &|q| {
        q.sumcheck.pop();
    });
    add("roots long".into(), &|q| q.roots.push([0u8; 32]));
    add("round salts short".into(), &|q| {
        q.round_salts.pop();
    });
    add("queries short".into(), &|q| {
        q.queries.pop();
    });
    add("queries long".into(), &|q| {
        let x = q.queries[0].clone();
        q.queries.push(x)
    });
    for i in [0, pr.queries.len() / 2, pr.queries.len() - 1] {
        add(format!("q{i} level0 a"), &|q| q.queries[i].level0.a = q.queries[i].level0.a + Fp::ONE);
        add(format!("q{i} level0 b"), &|q| q.queries[i].level0.b = q.queries[i].level0.b + Fp::ONE);
        add(format!("q{i} level0 salt"), &|q| q.queries[i].level0.salt[31] ^= 0x80);
        add(format!("q{i} level0 salt short"), &|q| {
            q.queries[i].level0.salt.pop();
        });
        add(format!("q{i} level0 path"), &|q| q.queries[i].level0.path[0][0] ^= 1);
        add(format!("q{i} level0 path top"), &|q| {
            let l = q.queries[i].level0.path.len() - 1;
            q.queries[i].level0.path[l][31] ^= 1
        });
        add(format!("q{i} level0 path short"), &|q| {
            q.queries[i].level0.path.pop();
        });
        add(format!("q{i} level0 path long"), &|q| q.queries[i].level0.path.push([0u8; 32]));
        for j in 0..pr.queries[i].levels.len() {
            add(format!("q{i} level{} a", j + 1), &|q| {
                q.queries[i].levels[j].a = q.queries[i].levels[j].a + E::ONE
            });
            add(format!("q{i} level{} b", j + 1), &|q| {
                q.queries[i].levels[j].b = q.queries[i].levels[j].b + E::ONE
            });
            add(format!("q{i} level{} salt", j + 1), &|q| q.queries[i].levels[j].salt[5] ^= 4);
            add(format!("q{i} level{} path", j + 1), &|q| q.queries[i].levels[j].path[0][9] ^= 2);
            add(format!("q{i} level{} path short", j + 1), &|q| {
                q.queries[i].levels[j].path.pop();
            });
        }
        add(format!("q{i} levels short"), &|q| {
            q.queries[i].levels.pop();
        });
    }
    // swap two queries
    add("swap queries".into(), &|q| q.queries.swap(0, 1));
    out
}

fn all_mutations_rejected<E: ExtField>(m: usize, s: usize, seed: u64) {
    let mut rng = Rng(seed);
    let p = Params::new(m, 2, s, 24);
    let table: Vec<Fp> = (0..1 << m).map(|_| rng.fp()).collect();
    let z: Vec<E> = (0..m).map(|_| rng.ext()).collect();
    let (root, pd) = commit(&p, &table).unwrap();
    let (v, proof) = open(&p, &pd, &z).unwrap();
    assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()));
    let muts = mutations(&proof);
    assert!(muts.len() > 50);
    for (name, bad) in muts {
        if bad == proof {
            continue; // e.g. swapping two equal queries
        }
        let r = catch_unwind(AssertUnwindSafe(|| verify(&p, &root, &z, v, &bad)));
        match r {
            Ok(res) => assert!(res.is_err(), "accepted mutation: {name} (m={m}, s={s})"),
            Err(_) => panic!("verifier panicked on mutation: {name} (m={m}, s={s})"),
        }
    }
}

#[test]
fn single_mutations_quadratic() {
    all_mutations_rejected::<Fp2>(8, 5, 1);
    all_mutations_rejected::<Fp2>(10, 10, 2);
    all_mutations_rejected::<Fp2>(6, 2, 3);
}

#[test]
fn single_mutations_quartic() {
    all_mutations_rejected::<Fp4>(8, 4, 4);
    all_mutations_rejected::<Fp4>(9, 9, 5);
}

#[test]
fn random_corruption_never_panics() {
    let mut rng = Rng(77);
    for s in [0, 1, 3, 6] {
        let p = Params::new(6, 2, s, 12);
        let table: Vec<Fp> = (0..64).map(|_| rng.fp()).collect();
        let z: Vec<Fp2> = (0..6).map(|_| rng.ext()).collect();
        let (root, pd) = commit(&p, &table).unwrap();
        let (v, proof) = open(&p, &pd, &z).unwrap();
        for _ in 0..500 {
            let mut bad = proof.clone();
            // truncate or extend random vectors, or empty them
            match rng.below(6) {
                0 => bad.sumcheck.truncate(rng.below(bad.sumcheck.len() + 1)),
                1 => bad.roots.clear(),
                2 => bad.g.truncate(rng.below(bad.g.len() + 1)),
                3 => {
                    let i = rng.below(bad.queries.len());
                    bad.queries[i].level0.path.truncate(rng.below(8));
                }
                4 => {
                    let i = rng.below(bad.queries.len());
                    bad.queries[i].levels.truncate(rng.below(s + 1));
                }
                _ => {
                    let j = rng.below(bad.round_salts.len());
                    bad.round_salts[j].truncate(rng.below(40));
                }
            }
            let r = catch_unwind(AssertUnwindSafe(|| verify(&p, &root, &z, v, &bad)));
            assert!(r.is_ok(), "verifier panicked (s={s})");
            if bad != proof {
                assert!(r.unwrap().is_err());
            }
        }
    }
}
