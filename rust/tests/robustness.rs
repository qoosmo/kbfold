//! Every single mutation of an honest proof is rejected, and the verifier never panics on
//! malformed proofs (wrong lengths, truncated salts and paths, random corruption).

use kbfold::field::{ExtField, Field, Fp, Fp2, Fp4};
use kbfold::pcs::{LevelOpening, Params, Proof, commit, open, verify};
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

fn level_mutations<F: Field>(
    name: &str,
    o: &LevelOpening<F>,
    set: &dyn Fn(&mut Proof<Fp2>, LevelOpening<F>),
    base: &Proof<Fp2>,
    out: &mut Vec<(String, Proof<Fp2>)>,
) {
    let mut add = |n: String, f: &dyn Fn(&mut LevelOpening<F>)| {
        let mut q = base.clone();
        let mut l = o.clone();
        f(&mut l);
        set(&mut q, l);
        out.push((format!("{name} {n}"), q));
    };
    for i in [0, o.values.len() / 2, o.values.len() - 1] {
        for u in [0, o.values[i].len() - 1] {
            add(format!("value {i} {u}"), &|l| {
                l.values[i][u] = l.values[i][u] + F::ONE
            });
        }
        add(format!("salt {i}"), &|l| l.salts[i][3] ^= 8);
        add(format!("salt {i} short"), &|l| {
            l.salts[i].pop();
        });
        add(format!("values {i} short"), &|l| {
            l.values[i].pop();
        });
        add(format!("values {i} long"), &|l| l.values[i].push(F::ZERO));
    }
    for k in 0..o.nodes.len() {
        add(format!("node {k}"), &|l| l.nodes[k][k % 32] ^= 1);
    }
    add("nodes short".into(), &|l| {
        l.nodes.pop();
    });
    add("nodes long".into(), &|l| l.nodes.push([0u8; 32]));
    add("leaves short".into(), &|l| {
        l.values.pop();
        l.salts.pop();
    });
    add("leaves swapped".into(), &|l| {
        l.values.swap(0, 1);
        l.salts.swap(0, 1);
    });
}

/// All single mutations of a proof: each changes one value, one byte, or one length.
fn mutations(pr: &Proof<Fp2>) -> Vec<(String, Proof<Fp2>)> {
    let mut out = Vec::new();
    {
        let mut add = |name: String, f: &dyn Fn(&mut Proof<Fp2>)| {
            let mut q = pr.clone();
            f(&mut q);
            out.push((name, q));
        };
        for j in 0..pr.sumcheck.len() {
            for k in 0..3 {
                add(format!("sumcheck {j} {k}"), &|q| {
                    q.sumcheck[j][k] = q.sumcheck[j][k] + Fp2::ONE
                });
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
            add(format!("round salt {j} long"), &|q| {
                q.round_salts[j].push(0)
            });
        }
        for k in 0..pr.g.len() {
            add(format!("g {k}"), &|q| q.g[k] = q.g[k] + Fp2::ONE);
        }
        add("g short".into(), &|q| {
            q.g.pop();
        });
        add("g long".into(), &|q| q.g.push(Fp2::ZERO));
        add("sumcheck short".into(), &|q| {
            q.sumcheck.pop();
        });
        add("roots long".into(), &|q| q.roots.push([0u8; 32]));
        add("round salts short".into(), &|q| {
            q.round_salts.pop();
        });
        add("levels short".into(), &|q| {
            q.levels.pop();
        });
    }
    level_mutations("level0", &pr.level0, &|q, l| q.level0 = l, pr, &mut out);
    for i in 0..pr.levels.len() {
        level_mutations(
            &format!("level{i}"),
            &pr.levels[i],
            &|q, l| q.levels[i] = l,
            pr,
            &mut out,
        );
    }
    out
}

fn all_mutations_rejected(m: usize, s: usize, k: usize, seed: u64) {
    let mut rng = Rng(seed);
    let p = Params {
        fold_log: k,
        ..Params::new(m, 2, s, 24)
    };
    let table: Vec<Fp> = (0..1 << m).map(|_| rng.fp()).collect();
    let z: Vec<Fp2> = (0..m).map(|_| rng.ext()).collect();
    let (root, pd) = commit(&p, &table).unwrap();
    let (v, proof) = open(&p, &pd, &z).unwrap();
    assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()));
    let muts = mutations(&proof);
    assert!(muts.len() > 50);
    for (name, bad) in muts {
        if bad == proof {
            continue;
        }
        let r = catch_unwind(AssertUnwindSafe(|| verify(&p, &root, &z, v, &bad)));
        match r {
            Ok(res) => assert!(
                res.is_err(),
                "accepted mutation: {name} (m={m}, s={s}, k={k})"
            ),
            Err(_) => panic!("verifier panicked on mutation: {name} (m={m}, s={s}, k={k})"),
        }
    }
}

#[test]
fn single_mutations() {
    all_mutations_rejected(8, 5, 1, 1);
    all_mutations_rejected(10, 10, 4, 2);
    all_mutations_rejected(6, 2, 4, 3);
    all_mutations_rejected(10, 7, 3, 4);
    all_mutations_rejected(9, 9, 2, 5);
}

#[test]
fn quartic_proofs_verify_and_reject() {
    let mut rng = Rng(9);
    let p = Params::new(9, 2, 7, 30);
    let table: Vec<Fp> = (0..1 << 9).map(|_| rng.fp()).collect();
    let z: Vec<Fp4> = (0..9).map(|_| rng.ext()).collect();
    let (root, pd) = commit(&p, &table).unwrap();
    let (v, mut proof) = open(&p, &pd, &z).unwrap();
    assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()));
    proof.levels[0].values[0][3] = proof.levels[0].values[0][3] + Fp4::ONE;
    assert!(verify(&p, &root, &z, v, &proof).is_err());
}

#[test]
fn random_corruption_never_panics() {
    let mut rng = Rng(77);
    for (s, k) in [(0, 4), (1, 1), (3, 2), (6, 4), (6, 1)] {
        let p = Params {
            fold_log: k,
            ..Params::new(6, 2, s, 12)
        };
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
                    let l = rng.below(bad.level0.nodes.len() + 1);
                    bad.level0.nodes.truncate(l);
                    let l = rng.below(bad.level0.values.len() + 1);
                    bad.level0.values.truncate(l);
                }
                4 => {
                    if let Some(o) = bad.levels.last_mut() {
                        let l = rng.below(o.values[0].len() + 1);
                        o.values[0].truncate(l);
                        o.salts.clear();
                    }
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
