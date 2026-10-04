//! The evaluation protocol `Pi_eval^J` of Sections 5.2-5.3 and the sum protocol `Pi_sum`,
//! compiled as in KBFold (salted BLAKE3 Merkle trees over fibres and cosets, one round salt per
//! round, Fiat-Shamir challenges from the roots and salts of all previous rounds, merged
//! authentication paths).
//!
//! * Commitment: `w_0 = Enc(f) = ev_L(V_f)`, `V_f = sum_a f(a) X^a`; the table is the coefficient
//!   vector, so the commitment is one zero-padded NTT of the table (no basis transform).
//! * Round `j`: the prover sends the linear coefficient `b_j` of `s_j(T) = a_j + b_j T`
//!   (Remark 5.4); the verifier sets `a_j = v_{j-1} - z_j b_j`, draws `theta_j`, and sets
//!   `v_j = a_j + theta_j b_j`. The prover restricts its table, `f_j = cres_{theta_j}(f_{j-1})`.
//! * Folding: the classical fold `w_e + theta w_o` (Definition 4.5), shared challenges.
//! * Closure: `v_s = P_g(z_{s+1}, ..., z_m)`; queries: the local coset folds of KBFold, against
//!   `G = V_g`, whose coefficient vector is `g` itself.
//!
//! Tables live over the base field F_p (Goldilocks); challenges, the point and the folded words
//! over an extension `E` ([`Fp2`](kbfold::field::Fp2) or [`Fp4`](kbfold::field::Fp4)).

use kbfold::error::Error;
use kbfold::field::{ExtField, Field, Fp};
use kbfold::merkle::{Digest, MerkleTree, Transcript, fibre_leaf, leaf_values, verify_multi};
use kbfold::pcs::LevelOpening;
use kbfold::poly::{horner, ntt};

use crate::rand::{derive, fresh_seed};

/// Domain separator of the transcript; changes with the proof format.
pub const LABEL: &[u8] = b"sumfri/v0.1/pcs";

/// Parameters of the scheme (the notation of the KBFold crate: `m` variables, `s` folding rounds).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    /// number of variables m (N = 2^m)
    pub m: usize,
    /// R with rate rho = 2^-R
    pub log_inv_rate: usize,
    /// number of folding rounds s (the paper's ell), 0 <= s <= m
    pub s: usize,
    /// number of queries kappa
    pub queries: usize,
    /// length in bytes of the leaf salts and of the round salts (0 = unsalted, for measurements)
    pub salt_len: usize,
    /// k: variables folded between two committed words (1 <= k <= 6)
    pub fold_log: usize,
}

impl Params {
    /// 32-byte salts, folding 4 variables between committed words.
    pub fn new(m: usize, log_inv_rate: usize, s: usize, queries: usize) -> Self {
        Params {
            m,
            log_inv_rate,
            s,
            queries,
            salt_len: 32,
            fold_log: 4,
        }
    }
    /// Classical parameters (use with `Fp2`): rate 1/4, final table of 16 elements, 148 queries.
    pub fn classical(m: usize) -> Self {
        Self::new(m, 2, m.saturating_sub(4), 148)
    }
    /// Post-quantum parameters of Remark 6.29 (use with `Fp4`): rate 1/4, 248 queries.
    pub fn post_quantum(m: usize) -> Self {
        Self::new(m, 2, m.saturating_sub(4), 248)
    }
    /// Size M = 2^(m+R) of the evaluation domain.
    pub fn n(&self) -> usize {
        1 << (self.m + self.log_inv_rate)
    }
    pub(crate) fn omega(&self) -> Fp {
        Fp::two_adic_root((self.m + self.log_inv_rate) as u32)
    }
    /// The committed levels with their group sizes, `(0, g_0), (k, g_1), ...` (as in KBFold).
    pub fn groups(&self) -> Vec<(usize, usize)> {
        if self.s == 0 {
            return vec![(0, 1)];
        }
        let mut out = Vec::new();
        let mut j = 0;
        while j < self.s {
            let g = self.fold_log.min(self.s - j);
            out.push((j, g));
            j += g;
        }
        out
    }
    /// Checks the parameters; every prover and verifier of this module calls it first.
    pub fn validate(&self) -> Result<(), Error> {
        if self.m == 0 {
            return Err(Error::Params("need m >= 1"));
        }
        if self.log_inv_rate == 0 {
            return Err(Error::Params("need log_inv_rate >= 1"));
        }
        if self.m + self.log_inv_rate > 32 {
            return Err(Error::Params("need m + log_inv_rate <= 32"));
        }
        if self.s > self.m {
            return Err(Error::Params("need s <= m"));
        }
        if self.queries == 0 || self.queries > 4096 {
            return Err(Error::Params("need 1 <= queries <= 4096"));
        }
        if self.salt_len > 64 {
            return Err(Error::Params("need salt_len <= 64"));
        }
        if self.fold_log == 0 || self.fold_log > 6 {
            return Err(Error::Params("need 1 <= fold_log <= 6"));
        }
        Ok(())
    }
}

/// The prover's state after `commit`: the table, the codeword `w_0` and its salted tree.
pub struct ProverData {
    table: Vec<Fp>,
    w0: Vec<Fp>,
    tree0: MerkleTree,
}

impl ProverData {
    /// Root of the commitment tree.
    pub fn root(&self) -> Digest {
        self.tree0.root()
    }
    /// The committed codeword `w_0 = Enc(f)`.
    pub fn codeword(&self) -> &[Fp] {
        &self.w0
    }
}

/// A proof of `Pi_eval^J`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof<E> {
    /// the linear coefficients b_j of the round polynomials, j = 1 .. s
    pub rounds: Vec<E>,
    /// roots of the committed words w_k, w_2k, ... (levels below s)
    pub roots: Vec<Digest>,
    /// round salts of rounds 1 .. s+1
    pub round_salts: Vec<Vec<u8>>,
    /// final table g (N / 2^s entries)
    pub g: Vec<E>,
    /// openings of w_0
    pub level0: LevelOpening<Fp>,
    /// openings of the other committed words, in the order of `roots`
    pub levels: Vec<LevelOpening<E>>,
}

impl<E: ExtField> Proof<E> {
    /// Serialized size in bytes: the length of [`Proof::to_bytes`].
    pub fn size_bytes(&self) -> usize {
        self.to_bytes().len()
    }
    /// Canonical encoding: the b_j, the roots, the round salts, g, then for w_0 and each other
    /// committed word the opened leaves (values, then salt) and the merged path nodes. No length
    /// prefixes: all lengths are fixed by the parameters and the query points.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for x in &self.rounds {
            x.to_bytes(&mut out);
        }
        for r in &self.roots {
            out.extend_from_slice(r);
        }
        for x in &self.round_salts {
            out.extend_from_slice(x);
        }
        for x in &self.g {
            x.to_bytes(&mut out);
        }
        fn level<F: Field>(o: &LevelOpening<F>, out: &mut Vec<u8>) {
            for (vals, salt) in o.values.iter().zip(&o.salts) {
                for v in vals {
                    v.to_bytes(out);
                }
                out.extend_from_slice(salt);
            }
            for d in &o.nodes {
                out.extend_from_slice(d);
            }
        }
        level(&self.level0, &mut out);
        for o in &self.levels {
            level(o, &mut out);
        }
        out
    }
}

/// Commits to a table `f` over F_p of length 2^m: `Enc(f)` (zero-padding and one NTT of size M,
/// no basis transform) and its salted Merkle tree over fibres.
pub fn commit(p: &Params, table: &[Fp]) -> Result<(Digest, ProverData), Error> {
    commit_seeded(p, table, &fresh_seed()?)
}

pub(crate) fn commit_seeded(
    p: &Params,
    table: &[Fp],
    seed: &Digest,
) -> Result<(Digest, ProverData), Error> {
    p.validate()?;
    if table.len() != 1 << p.m {
        return Err(Error::Input("table length must be 2^m"));
    }
    let mut w0 = table.to_vec();
    w0.resize(p.n(), Fp::ZERO);
    ntt(&mut w0, p.omega());
    let g0 = p.groups()[0].1;
    let tree0 = MerkleTree::new_fibres(&w0, g0, seed, b"w0", p.salt_len);
    let root = tree0.root();
    Ok((
        root,
        ProverData {
            table: table.to_vec(),
            w0,
            tree0,
        },
    ))
}

/// Classical fold (Lemma 4.8(3)): `cfold_t(w)(x^2) = w_e + t w_o`, `w_e = (a+b)/2`,
/// `w_o = (a-b)/(2x)`, `a = w(x)`, `b = w(-x)`.
#[inline(always)]
pub(crate) fn cfold_pair<E: ExtField>(a: E, b: E, inv_2x: Fp, t: E, inv2: Fp) -> E {
    (a + b) * inv2 + t * ((a - b) * inv_2x)
}

/// Folds a whole word on L_j to L_{j+1}. `inv_x0[k] = omega^{-k}` for k < M/2.
fn cfold_word<F: Field, E: ExtField + From<F>>(
    w: &[F],
    t: E,
    inv_x0: &[Fp],
    level: usize,
    inv2: Fp,
) -> Vec<E> {
    let h = w.len() / 2;
    crate::par::map_range(h, |i| {
        let inv_2x = inv_x0[i << level] * inv2;
        cfold_pair(E::from(w[i]), E::from(w[i + h]), inv_2x, t, inv2)
    })
}

/// The monomial table `tau(a) = prod_k z_k^{a_k}` of a point (bit k of a is the variable k+1).
pub fn monomial_table<E: ExtField>(z: &[E]) -> Vec<E> {
    let mut t = Vec::with_capacity(1 << z.len());
    t.push(E::ONE);
    for &zk in z {
        let len = t.len();
        for i in 0..len {
            let x = t[i] * zk;
            t.push(x);
        }
    }
    t
}

/// Coefficient restriction `cres_t(f)(b') = f(2b') + t f(2b'+1)` (Definition 4.3).
pub fn cres<E: ExtField>(f: &[E], t: E) -> Vec<E> {
    crate::par::map_range(f.len() / 2, |i| f[2 * i] + t * f[2 * i + 1])
}

/// `P_f(y)` for a table `f` with `|y|` variables, by successive restrictions (O(|f|)).
pub fn cpoly_eval<E: ExtField>(f: &[E], y: &[E]) -> E {
    assert_eq!(f.len(), 1 << y.len());
    let mut cur = f.to_vec();
    for &yk in y {
        cur = (0..cur.len() / 2).map(|i| cur[2 * i] + yk * cur[2 * i + 1]).collect();
    }
    cur[0]
}

/// `b_j = sum_{b'} f(2b'+1) tau_j(b')` with `tau_j(b') = tau_0(b' << j)`, and the value
/// `a_j = sum f(2b') tau_j(b')` (used only by the cheating prover of the tests). With `ones`
/// (the point `1`), the tensor is skipped and the sums are plain additions.
fn round_coeffs<E: ExtField>(f: &[E], tau0: &[E], j: usize, ones: bool) -> (E, E) {
    let pairs = f.len() / 2;
    let block = crate::par::GRAIN;
    let parts = crate::par::map_range(pairs.div_ceil(block), |c| {
        let (mut a, mut b) = (E::ZERO, E::ZERO);
        for i in c * block..((c + 1) * block).min(pairs) {
            if ones {
                a = a + f[2 * i];
                b = b + f[2 * i + 1];
            } else {
                let t = tau0[i << j];
                a = a + f[2 * i] * t;
                b = b + f[2 * i + 1] * t;
            }
        }
        (a, b)
    });
    parts
        .iter()
        .fold((E::ZERO, E::ZERO), |(sa, sb), &(a, b)| (sa + a, sb + b))
}

pub(crate) fn init_transcript<E: ExtField>(p: &Params, root: &Digest, z: &[E], v: E) -> Transcript {
    let mut tr = Transcript::new(LABEL);
    let params = [
        p.m as u64,
        p.log_inv_rate as u64,
        p.s as u64,
        p.queries as u64,
        p.salt_len as u64,
        E::DEGREE as u64,
        p.fold_log as u64,
    ];
    let pb: Vec<u8> = params.iter().flat_map(|x| x.to_le_bytes()).collect();
    tr.absorb(b"params", &pb);
    tr.absorb(b"root0", root);
    tr.absorb_field(b"point", z);
    tr.absorb_field(b"value", &[v]);
    tr
}

/// Prover of `Pi_eval`: returns `v = P_f(z)` and the proof.
pub fn open<E: ExtField>(p: &Params, pd: &ProverData, z: &[E]) -> Result<(E, Proof<E>), Error> {
    open_inner(p, pd, z, &fresh_seed()?, None)
}

/// Prover of `Pi_sum`: returns `v = sum_a f(a)` and the proof (the point `z = 1`).
pub fn open_sum<E: ExtField>(p: &Params, pd: &ProverData) -> Result<(E, Proof<E>), Error> {
    open(p, pd, &vec![E::ONE; p.m])
}

#[cfg(feature = "insecure-test-vectors")]
pub(crate) fn open_seeded<E: ExtField>(
    p: &Params,
    pd: &ProverData,
    z: &[E],
    seed: &Digest,
) -> Result<(E, Proof<E>), Error> {
    open_inner(p, pd, z, seed, None)
}

/// `cheat = Some(d)`: claim `v + d`, send the honest `b_j` (so the restriction checks hold by
/// construction), fold honestly, and change `g(0)` so that the closure check passes. Used by the
/// tests: Theorem 6.13(2) predicts rejection in the query phase.
pub(crate) fn open_inner<E: ExtField>(
    p: &Params,
    pd: &ProverData,
    z: &[E],
    seed: &Digest,
    cheat: Option<E>,
) -> Result<(E, Proof<E>), Error> {
    p.validate()?;
    if z.len() != p.m {
        return Err(Error::Input("point length must be m"));
    }
    if pd.table.len() != 1 << p.m || pd.w0.len() != p.n() {
        return Err(Error::Input("prover data does not match the parameters"));
    }
    let n = p.n();
    let inv2 = Fp::new(2).inv();
    let omega_inv = p.omega().inv();
    let mut inv_x0 = Vec::with_capacity(n / 2);
    let mut acc = Fp::ONE;
    for _ in 0..n / 2 {
        inv_x0.push(acc);
        acc = acc * omega_inv;
    }
    let round_salt = |r: usize| derive(seed, b"round-salt", r as u64, p.salt_len);

    let ones = z.iter().all(|&x| x == E::ONE);
    let tau0: Vec<E> = if ones { Vec::new() } else { monomial_table(z) };
    let mut f: Vec<E> = pd.table.iter().map(|&x| E::from(x)).collect();
    let mut v = if ones {
        f.iter().fold(E::ZERO, |s, &x| s + x)
    } else {
        f.iter().zip(&tau0).fold(E::ZERO, |s, (&x, &t)| s + x * t)
    };
    if let Some(d) = cheat {
        v = v + d;
    }
    let mut claim = v;
    let mut tr = init_transcript(p, &pd.tree0.root(), z, v);

    let groups = p.groups();
    let committed = |j: usize| groups.iter().any(|&(l, _)| l == j);
    let group_of = |j: usize| groups.iter().find(|&&(l, _)| l == j).map_or(1, |&(_, g)| g);

    let mut rounds = Vec::with_capacity(p.s);
    let mut ts: Vec<E> = Vec::with_capacity(p.s);
    let mut roots = Vec::new();
    let mut round_salts = Vec::with_capacity(p.s + 1);
    let mut words: Vec<Vec<E>> = Vec::new(); // w_1 .. w_{s-1}
    let mut trees: Vec<(usize, MerkleTree)> = Vec::new();
    for j in 1..=p.s {
        let (_, b) = round_coeffs(&f, &tau0, j, ones);
        tr.absorb_field(b"round", &[b]);
        rounds.push(b);
        if j >= 2 {
            let t = ts[j - 2];
            let next = if j == 2 {
                cfold_word(&pd.w0, t, &inv_x0, 0, inv2)
            } else {
                cfold_word(&words[j - 3], t, &inv_x0, j - 2, inv2)
            };
            if committed(j - 1) {
                let label = format!("w{}", j - 1);
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
        let t: E = tr.challenge();
        // a_j = v_{j-1} - z_j b_j (equal to the honest a_j when the claim is honest)
        let a = claim - z[j - 1] * b;
        claim = a + t * b;
        ts.push(t);
        f = cres(&f, t);
    }
    let mut g = f;
    if cheat.is_some() {
        // make the closure check pass by changing g(0); tau_s(0) = 1
        let cur = cpoly_eval(&g, &z[p.s..]);
        g[0] = g[0] + (claim - cur);
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
        Proof {
            rounds,
            roots,
            round_salts,
            g,
            level0,
            levels,
        },
    ))
}

pub(crate) fn positions(indices: &[usize], len: usize, g: usize) -> Vec<usize> {
    let leaves = len >> g;
    let mut pos: Vec<usize> = indices.iter().map(|&i| i % leaves).collect();
    pos.sort_unstable();
    pos.dedup();
    pos
}

pub(crate) fn level0_positions(indices: &[usize], n: usize, g0: usize) -> Vec<usize> {
    let mut pos: Vec<usize> = positions(indices, n, g0)
        .iter()
        .flat_map(|&t| (0..1usize << (g0 - 1)).map(move |u| (t << (g0 - 1)) + u))
        .collect();
    pos.sort_unstable();
    pos
}

pub(crate) fn open_level<F: Field>(w: &[F], tree: &MerkleTree, g: usize, pos: &[usize]) -> LevelOpening<F> {
    LevelOpening {
        values: pos.iter().map(|&t| leaf_values(w, g, t)).collect(),
        salts: pos.iter().map(|&t| tree.salt(t)).collect(),
        nodes: tree.multi_path(pos),
    }
}

pub(crate) fn check_level<F: Field>(
    p: &Params,
    root: &Digest,
    o: &LevelOpening<F>,
    len: usize,
    g: usize,
    pos: &[usize],
) -> Result<(), Error> {
    if o.values.len() != pos.len()
        || o.salts.len() != pos.len()
        || o.values.iter().any(|v| v.len() != 1 << g)
        || o.salts.iter().any(|x| x.len() != p.salt_len)
    {
        return Err(Error::Shape);
    }
    let leaves: Vec<(usize, &[F], &[u8])> = pos
        .iter()
        .enumerate()
        .map(|(i, &t)| (t, o.values[i].as_slice(), o.salts[i].as_slice()))
        .collect();
    let depth = (len >> g).trailing_zeros() as usize;
    if verify_multi(root, depth, &leaves, &o.nodes) {
        Ok(())
    } else {
        Err(Error::Merkle)
    }
}

/// Verifier of `Pi_eval`: `Ok(())` if the proof of `P_f(z) = v` is accepted. Never panics on a
/// malformed proof.
pub fn verify<E: ExtField>(
    p: &Params,
    root: &Digest,
    z: &[E],
    v: E,
    proof: &Proof<E>,
) -> Result<(), Error> {
    p.validate()?;
    let n = p.n();
    let s = p.s;
    let groups = p.groups();
    if z.len() != p.m {
        return Err(Error::Input("point length must be m"));
    }
    if proof.rounds.len() != s
        || proof.roots.len() != groups.len() - 1
        || proof.levels.len() != groups.len() - 1
        || proof.round_salts.len() != s + 1
        || proof.round_salts.iter().any(|x| x.len() != p.salt_len)
        || proof.g.len() != 1 << (p.m - s)
    {
        return Err(Error::Shape);
    }
    let omega = p.omega();
    let omega_inv = omega.inv();
    let inv2 = Fp::new(2).inv();
    let mut tr = init_transcript(p, root, z, v);

    // rounds 1 .. s: restriction checks hold by construction (Remark 5.4)
    let mut claim = v;
    let mut ts: Vec<E> = Vec::with_capacity(s);
    let mut next_root = 0;
    for j in 1..=s {
        let b = proof.rounds[j - 1];
        tr.absorb_field(b"round", &[b]);
        if j >= 2 && groups.iter().any(|&(l, _)| l == j - 1) {
            tr.absorb(b"root", &proof.roots[next_root]);
            next_root += 1;
        }
        tr.absorb(b"salt", &proof.round_salts[j - 1]);
        let t: E = tr.challenge();
        let a = claim - z[j - 1] * b;
        claim = a + t * b;
        ts.push(t);
    }
    tr.absorb_field(b"final", &proof.g);
    tr.absorb(b"salt", &proof.round_salts[s]);
    let indices = tr.query_indices(p.queries, p.m + p.log_inv_rate);

    // closure: v_s = P_g(z_{s+1}, ..., z_m)
    if claim != cpoly_eval(&proof.g, &z[s..]) {
        return Err(Error::Check("closure"));
    }

    // Merkle openings of every committed word
    let g0 = groups[0].1;
    let mut pos: Vec<Vec<usize>> = groups
        .iter()
        .map(|&(j, g)| positions(&indices, n >> j, g))
        .collect();
    pos[0] = level0_positions(&indices, n, g0);
    check_level(p, root, &proof.level0, n, 1, &pos[0])?;
    for (i, &(j, g)) in groups.iter().enumerate().skip(1) {
        check_level(
            p,
            &proof.roots[i - 1],
            &proof.levels[i - 1],
            n >> j,
            g,
            &pos[i],
        )?;
    }

    // G = V_g: its coefficient vector is g
    let gc = &proof.g;
    let leaf_of = |i: usize, t: usize| pos[i].binary_search(&t).expect("t is an opened leaf");
    for &i0 in &indices {
        if s == 0 {
            let t = i0 % (n / 2);
            let val = E::from(proof.level0.values[leaf_of(0, t)][i0 / (n / 2)]);
            if val != horner(gc, E::from(omega.pow(i0 as u64))) {
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
                (0..2 * half)
                    .map(|u| {
                        E::from(
                            proof.level0.values[leaf_of(0, (t << (g - 1)) + u % half)][u / half],
                        )
                    })
                    .collect()
            } else {
                proof.levels[i - 1].values[leaf_of(i, t)].clone()
            };
            if let Some(c) = carried {
                if cur[(i0 % mj) / leaves] != c {
                    return Err(Error::Fold);
                }
            }
            let mut x_inv = omega_inv.pow((t as u64) << j);
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
        let y = omega.pow(((i0 % (n >> s)) as u64) << s);
        if carried != Some(horner(gc, E::from(y))) {
            return Err(Error::Fold);
        }
    }
    Ok(())
}

/// Verifier of `Pi_sum`: `Ok(())` if the proof of `sum_a f(a) = v` is accepted.
pub fn verify_sum<E: ExtField>(
    p: &Params,
    root: &Digest,
    v: E,
    proof: &Proof<E>,
) -> Result<(), Error> {
    verify(p, root, &vec![E::ONE; p.m], v, proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use kbfold::field::{Fp2, Fp4};

    /// Commits `Enc(f)` honestly, claims `v + 1`, keeps the restriction checks (by construction)
    /// and the closure check satisfied. Theorem 6.13(2) predicts rejection in the query phase.
    fn cheater_rejected<E: ExtField>(mk: impl Fn(Fp, Fp) -> E) {
        let mut x = 99u64;
        let mut rnd = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            Fp::new(x)
        };
        for (m, s, k) in [(6, 3, 1), (8, 5, 2), (8, 8, 4), (10, 6, 3), (10, 9, 4)] {
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
            for z in [
                (0..m).map(|_| mk(rnd(), rnd())).collect::<Vec<E>>(),
                vec![E::ONE; m],
            ] {
                let (v, proof) = open_inner(&p, &pd, &z, &[3u8; 32], Some(E::ONE)).unwrap();
                assert_eq!(verify(&p, &root, &z, v, &proof), Err(Error::Fold), "m={m} s={s}");
                let (v, proof) = open(&p, &pd, &z).unwrap();
                assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()));
            }
        }
    }

    #[test]
    fn consistent_restriction_cheater_is_rejected() {
        cheater_rejected(Fp2);
        cheater_rejected(|a, b| Fp4(Fp2(a, b), Fp2(b, a)));
    }
}
