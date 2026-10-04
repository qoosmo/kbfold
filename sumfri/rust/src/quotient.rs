//! Baseline of Section 8: the sum `sum_a f(a) = V_f(1)` proved as a univariate opening of the
//! committed polynomial at the point `1`, with the quotient `q = (V_f - v) / (X - 1)` and a FRI
//! low-degree test of `q` (the standard univariate opening in FRI-based systems).
//!
//! Since `1` lies in the smooth domain `L`, the commitment is `ev_{cL}(V_f)` on the coset `cL`,
//! `c = 7` (a generator of F_p^*, so `1 ∉ cL`). The verifier computes the values of `q` at the
//! opened points from those of the commitment. The folding, the committed levels, the trees, the
//! salts and the transcript are those of [`crate::pcs`]; there are no round messages, and the
//! final message is the coefficient vector of the folded quotient.

use kbfold::error::Error;
use kbfold::field::{ExtField, Field, Fp, GENERATOR, batch_inv};
use kbfold::merkle::{Digest, MerkleTree, Transcript, fibre_leaf};
use kbfold::pcs::LevelOpening;
use kbfold::poly::{horner, ntt};

use crate::pcs::{
    Params, cfold_pair, check_level, cres, level0_positions, open_level, positions,
};
use crate::rand::{derive, fresh_seed};

/// Domain separator of the transcript.
pub const LABEL: &[u8] = b"sumfri/v0.1/quotient";

/// The coset shift `c`.
pub const SHIFT: Fp = Fp::new(GENERATOR);

/// The prover's state: the table, the codeword `w_0 = ev_{cL}(V_f)` and its tree.
pub struct QProverData {
    table: Vec<Fp>,
    w0: Vec<Fp>,
    tree0: MerkleTree,
}

impl QProverData {
    pub fn root(&self) -> Digest {
        self.tree0.root()
    }
}

/// A proof of `V_f(1) = v`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QProof<E> {
    /// roots of the committed folded words (levels k, 2k, ... below s)
    pub roots: Vec<Digest>,
    /// round salts of rounds 1 .. s+1
    pub round_salts: Vec<Vec<u8>>,
    /// coefficient vector of the folded quotient (N / 2^s entries)
    pub g: Vec<E>,
    /// openings of w_0
    pub level0: LevelOpening<Fp>,
    /// openings of the other committed words
    pub levels: Vec<LevelOpening<E>>,
}

impl<E: ExtField> QProof<E> {
    /// Serialized size in bytes (same conventions as [`crate::pcs::Proof::to_bytes`]).
    pub fn size_bytes(&self) -> usize {
        let fe = 8 * E::DEGREE;
        let lvl = |vals: usize, salts: usize, nodes: usize, w: usize| vals * w + salts + 32 * nodes;
        let mut b = 32 * self.roots.len()
            + self.round_salts.iter().map(|x| x.len()).sum::<usize>()
            + fe * self.g.len();
        b += lvl(
            self.level0.values.iter().map(|v| v.len()).sum(),
            self.level0.salts.iter().map(|x| x.len()).sum(),
            self.level0.nodes.len(),
            8,
        );
        for o in &self.levels {
            b += lvl(
                o.values.iter().map(|v| v.len()).sum(),
                o.salts.iter().map(|x| x.len()).sum(),
                o.nodes.len(),
                fe,
            );
        }
        b
    }
}

/// Commits to `f` on the coset: `w_0(c omega^i) = V_f(c omega^i)`.
pub fn commit(p: &Params, table: &[Fp]) -> Result<(Digest, QProverData), Error> {
    commit_seeded(p, table, &fresh_seed()?)
}

pub(crate) fn commit_seeded(
    p: &Params,
    table: &[Fp],
    seed: &Digest,
) -> Result<(Digest, QProverData), Error> {
    p.validate()?;
    if table.len() != 1 << p.m {
        return Err(Error::Input("table length must be 2^m"));
    }
    let mut w0 = Vec::with_capacity(p.n());
    let mut c = Fp::ONE;
    for &x in table {
        w0.push(x * c);
        c = c * SHIFT;
    }
    w0.resize(p.n(), Fp::ZERO);
    ntt(&mut w0, p.omega());
    let tree0 = MerkleTree::new_fibres(&w0, p.groups()[0].1, seed, b"w0", p.salt_len);
    Ok((
        tree0.root(),
        QProverData {
            table: table.to_vec(),
            w0,
            tree0,
        },
    ))
}

fn transcript(p: &Params, root: &Digest, v: Fp) -> Transcript {
    let mut tr = Transcript::new(LABEL);
    let params = [
        p.m as u64,
        p.log_inv_rate as u64,
        p.s as u64,
        p.queries as u64,
        p.salt_len as u64,
        p.fold_log as u64,
    ];
    let pb: Vec<u8> = params.iter().flat_map(|x| x.to_le_bytes()).collect();
    tr.absorb(b"params", &pb);
    tr.absorb(b"root0", root);
    tr.absorb_field(b"value", &[v]);
    tr
}

/// Folds a word on the level-`j` coset `c^(2^j) L_j`.
fn cfold_word_coset<F: Field, E: ExtField + From<F>>(
    w: &[F],
    t: E,
    inv_x0: &[Fp],
    level: usize,
    cinv_j: Fp,
    inv2: Fp,
) -> Vec<E> {
    let h = w.len() / 2;
    crate::par::map_range(h, |i| {
        let inv_2x = inv_x0[i << level] * cinv_j * inv2;
        cfold_pair(E::from(w[i]), E::from(w[i + h]), inv_2x, t, inv2)
    })
}

/// Prover: `v = V_f(1) = sum_a f(a)` and the proof.
pub fn open<E: ExtField>(p: &Params, pd: &QProverData) -> Result<(Fp, QProof<E>), Error> {
    open_seeded(p, pd, &fresh_seed()?)
}

pub(crate) fn open_seeded<E: ExtField>(
    p: &Params,
    pd: &QProverData,
    seed: &Digest,
) -> Result<(Fp, QProof<E>), Error> {
    p.validate()?;
    if pd.table.len() != 1 << p.m || pd.w0.len() != p.n() {
        return Err(Error::Input("prover data does not match the parameters"));
    }
    let n = p.n();
    let big_n = 1usize << p.m;
    let inv2 = Fp::new(2).inv();
    let omega = p.omega();
    let omega_inv = omega.inv();
    let cinv = SHIFT.inv();
    let mut inv_x0 = Vec::with_capacity(n / 2);
    let mut acc = Fp::ONE;
    for _ in 0..n / 2 {
        inv_x0.push(acc);
        acc = acc * omega_inv;
    }
    let v = pd.table.iter().fold(Fp::ZERO, |s, &x| s + x);
    // q_k = sum_{i > k} f_i: V_f - v = (X - 1) q
    let mut qc = vec![Fp::ZERO; big_n];
    let mut suffix = Fp::ZERO;
    for k in (0..big_n - 1).rev() {
        suffix = suffix + pd.table[k + 1];
        qc[k] = suffix;
    }
    // the quotient word on the coset: (w_0 - v) / (x - 1)
    let mut x = SHIFT;
    let mut den = Vec::with_capacity(n);
    for _ in 0..n {
        den.push(x - Fp::ONE);
        x = x * omega;
    }
    let den_inv = batch_inv(&den);
    let qw: Vec<Fp> = (0..n).map(|i| (pd.w0[i] - v) * den_inv[i]).collect();

    let round_salt = |r: usize| derive(seed, b"q-round-salt", r as u64, p.salt_len);
    let mut tr = transcript(p, &pd.tree0.root(), v);
    let groups = p.groups();
    let committed = |j: usize| groups.iter().any(|&(l, _)| l == j);
    let group_of = |j: usize| groups.iter().find(|&&(l, _)| l == j).map_or(1, |&(_, g)| g);
    let mut ts: Vec<E> = Vec::with_capacity(p.s);
    let mut roots = Vec::new();
    let mut round_salts = Vec::with_capacity(p.s + 1);
    let mut words: Vec<Vec<E>> = Vec::new();
    let mut trees: Vec<(usize, MerkleTree)> = Vec::new();
    for j in 1..=p.s {
        if j >= 2 {
            let t = ts[j - 2];
            let cinv_j = cinv.pow(1 << (j - 2));
            let next = if j == 2 {
                cfold_word_coset(&qw, t, &inv_x0, 0, cinv_j, inv2)
            } else {
                cfold_word_coset(&words[j - 3], t, &inv_x0, j - 2, cinv_j, inv2)
            };
            if committed(j - 1) {
                let label = format!("q{}", j - 1);
                let tree =
                    MerkleTree::new(&next, group_of(j - 1), seed, label.as_bytes(), p.salt_len);
                tr.absorb(b"root", &tree.root());
                roots.push(tree.root());
                trees.push((j - 1, tree));
            }
            words.push(next);
        }
        round_salts.push(round_salt(j));
        tr.absorb(b"salt", round_salts.last().unwrap());
        ts.push(tr.challenge());
    }
    let mut g: Vec<E> = qc.iter().map(|&x| E::from(x)).collect();
    for &t in &ts {
        g = cres(&g, t);
    }
    tr.absorb_field(b"final", &g);
    round_salts.push(round_salt(p.s + 1));
    tr.absorb(b"salt", round_salts.last().unwrap());
    let indices = tr.query_indices(p.queries, p.m + p.log_inv_rate);

    let pos0 = level0_positions(&indices, n, groups[0].1);
    let level0 = LevelOpening {
        values: pos0
            .iter()
            .map(|&l| fibre_leaf(&pd.w0, groups[0].1, l))
            .collect(),
        salts: pos0.iter().map(|&l| pd.tree0.salt(l)).collect(),
        nodes: pd.tree0.multi_path(&pos0),
    };
    let levels = trees
        .iter()
        .map(|(j, tree)| {
            let gj = group_of(*j);
            open_level(&words[j - 1], tree, gj, &positions(&indices, n >> j, gj))
        })
        .collect();
    Ok((
        v,
        QProof {
            roots,
            round_salts,
            g,
            level0,
            levels,
        },
    ))
}

/// Verifier: `Ok(())` if the proof of `V_f(1) = v` is accepted.
pub fn verify<E: ExtField>(
    p: &Params,
    root: &Digest,
    v: Fp,
    proof: &QProof<E>,
) -> Result<(), Error> {
    p.validate()?;
    let n = p.n();
    let s = p.s;
    let groups = p.groups();
    if proof.roots.len() != groups.len() - 1
        || proof.levels.len() != groups.len() - 1
        || proof.round_salts.len() != s + 1
        || proof.round_salts.iter().any(|x| x.len() != p.salt_len)
        || proof.g.len() != 1 << (p.m - s)
    {
        return Err(Error::Shape);
    }
    // deg q < N - 1: the top coefficient of the unfolded quotient is 0, which the low-degree
    // test of degree < N does not see; it is not needed for soundness of V_f(1) = v.
    let omega = p.omega();
    let omega_inv = omega.inv();
    let inv2 = Fp::new(2).inv();
    let cinv = SHIFT.inv();
    let mut tr = transcript(p, root, v);
    let mut ts: Vec<E> = Vec::with_capacity(s);
    let mut next_root = 0;
    for j in 1..=s {
        if j >= 2 && groups.iter().any(|&(l, _)| l == j - 1) {
            tr.absorb(b"root", &proof.roots[next_root]);
            next_root += 1;
        }
        tr.absorb(b"salt", &proof.round_salts[j - 1]);
        ts.push(tr.challenge());
    }
    tr.absorb_field(b"final", &proof.g);
    tr.absorb(b"salt", &proof.round_salts[s]);
    let indices = tr.query_indices(p.queries, p.m + p.log_inv_rate);

    let g0 = groups[0].1;
    let mut pos: Vec<Vec<usize>> = groups
        .iter()
        .map(|&(j, g)| positions(&indices, n >> j, g))
        .collect();
    pos[0] = level0_positions(&indices, n, g0);
    check_level(p, root, &proof.level0, n, 1, &pos[0])?;
    for (i, &(j, g)) in groups.iter().enumerate().skip(1) {
        check_level(p, &proof.roots[i - 1], &proof.levels[i - 1], n >> j, g, &pos[i])?;
    }
    // the opened points of w_0 (indices into the level-0 word) and the batch-inverted
    // denominators 1/(x - 1) at these points
    let half0 = n / 2;
    let opened: Vec<usize> = if s == 0 {
        let mut v: Vec<usize> = indices.clone();
        v.sort_unstable();
        v.dedup();
        v
    } else {
        let leaves0 = n >> g0;
        let mut v: Vec<usize> = pos[0]
            .iter()
            .flat_map(|&l| {
                let (t, u) = (l >> (g0 - 1), l & ((1 << (g0 - 1)) - 1));
                let f = t + u * leaves0;
                [f, f + half0]
            })
            .collect();
        v.sort_unstable();
        v
    };
    let den: Vec<Fp> = opened
        .iter()
        .map(|&i| SHIFT * omega.pow(i as u64) - Fp::ONE)
        .collect();
    let den_inv = batch_inv(&den);
    let q_at = |w: Fp, idx: usize| -> Result<Fp, Error> {
        let k = opened.binary_search(&idx).map_err(|_| Error::Shape)?;
        Ok((w - v) * den_inv[k])
    };
    let leaf_of = |i: usize, t: usize| pos[i].binary_search(&t).expect("t is an opened leaf");
    for &i0 in &indices {
        if s == 0 {
            let t = i0 % (n / 2);
            let w = proof.level0.values[leaf_of(0, t)][i0 / (n / 2)];
            let x = SHIFT * omega.pow(i0 as u64);
            if E::from(q_at(w, i0)?) != horner(&proof.g, E::from(x)) {
                return Err(Error::Fold);
            }
            continue;
        }
        let mut carried: Option<E> = None;
        for (i, &(j, g)) in groups.iter().enumerate() {
            let mj = n >> j;
            let leaves = mj >> g;
            let t = i0 % leaves;
            let mut cur: Vec<E> = if i == 0 {
                let half = 1usize << (g - 1);
                let mut out = Vec::with_capacity(2 * half);
                for u in 0..2 * half {
                    let w = proof.level0.values[leaf_of(0, (t << (g - 1)) + u % half)][u / half];
                    out.push(E::from(q_at(w, t + u * leaves)?));
                }
                out
            } else {
                proof.levels[i - 1].values[leaf_of(i, t)].clone()
            };
            if let Some(c) = carried {
                if cur[(i0 % mj) / leaves] != c {
                    return Err(Error::Fold);
                }
            }
            // level-(j+h) points: c^(2^(j+h)) omega_{j+h}^(t) zeta_h^u
            let mut x_inv = omega_inv.pow((t as u64) << j) * cinv.pow(1 << j);
            for h in 0..g {
                let half = cur.len() / 2;
                let zeta_inv = omega_inv.pow((n >> (g - h)) as u64);
                let mut xu_inv = x_inv;
                let mut next = Vec::with_capacity(half);
                for u in 0..half {
                    next.push(cfold_pair(cur[u], cur[u + half], xu_inv * inv2, ts[j + h], inv2));
                    xu_inv = xu_inv * zeta_inv;
                }
                cur = next;
                x_inv = x_inv * x_inv;
            }
            carried = Some(cur[0]);
        }
        let y = SHIFT.pow(1 << s) * omega.pow(((i0 % (n >> s)) as u64) << s);
        if carried != Some(horner(&proof.g, E::from(y))) {
            return Err(Error::Fold);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use kbfold::field::Fp2;

    #[test]
    fn quotient_opening() {
        let mut x = 5u64;
        let mut rnd = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            Fp::new(x)
        };
        for (m, s, k) in [(1, 0, 1), (4, 0, 2), (6, 3, 1), (8, 8, 4), (10, 6, 3), (10, 9, 4)] {
            let p = Params {
                m,
                log_inv_rate: 2,
                s,
                queries: 20,
                salt_len: 32,
                fold_log: k,
            };
            let table: Vec<Fp> = (0..1 << m).map(|_| rnd()).collect();
            let (root, pd) = commit(&p, &table).unwrap();
            let (v, proof) = open::<Fp2>(&p, &pd).unwrap();
            assert_eq!(v, table.iter().fold(Fp::ZERO, |s, &x| s + x));
            assert_eq!(verify(&p, &root, v, &proof), Ok(()), "m={m} s={s}");
            assert!(verify(&p, &root, v + Fp::ONE, &proof).is_err());
        }
    }
}
