//! The evaluation protocol Pi_eval^J of Section 6.3 (committed levels J = {0, k, 2k, ...}),
//! compiled as in Section 3.4: salted BLAKE3 Merkle trees, one round salt per round, and
//! Fiat-Shamir challenges derived from the roots and salts of all previous rounds (the compiler
//! BCS of Chiesa-Di-Hu-Zheng, Construction 11.7). Openings of one committed word share one
//! merged authentication path.
//!
//! Tables live over the base field F_p (Goldilocks); challenges, evaluation points and all folded
//! words live over an extension `E`: [`Fp2`](crate::field::Fp2) for the classical parameters,
//! [`Fp4`](crate::field::Fp4) for the post-quantum parameters of Remark 7.28.

use crate::error::Error;
use crate::field::{ExtField, Field, Fp};
use crate::merkle::{Digest, MerkleTree, Transcript, fibre_leaf, leaf_values, verify_multi};
use crate::poly::{eq_table, horner, kernel_to_mono, mle_eval, mobius, ntt, restrict};
use crate::rand::{derive, fresh_seed};

/// Domain separator of the transcript; changes with the proof format.
pub const LABEL: &[u8] = b"kbfold/v0.3/pcs";

/// Encoding of the table.  `Kernel` is the scheme of the paper (U = sum_b f(b) K_b, kernel fold).
/// `Monomial` is the coefficient-form baseline (U = Kronecker embedding of the monomial
/// coefficients of f~, classical FRI fold U_e + T U_o), used for comparison in Section 9.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Basis {
    Kernel,
    Monomial,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    /// table encoding
    pub basis: Basis,
    /// number of variables m (N = 2^m)
    pub m: usize,
    /// R with rate rho = 2^-R
    pub log_inv_rate: usize,
    /// number of folding rounds s, 0 <= s <= m
    pub s: usize,
    /// number of queries kappa
    pub queries: usize,
    /// length in bytes of the leaf salts and of the round salts (32 = lambda_H / 8; 0 = unsalted,
    /// only to measure the cost of salting)
    pub salt_len: usize,
    /// k: variables folded between two committed words (1 <= k <= 6). The prover commits to
    /// w_0, w_k, w_2k, ... (levels below s); a leaf of the tree of w_j holds the 2^g values of a
    /// coset {x : x^(2^g) = y}, g = min(k, s - j), and the verifier folds g times locally.
    pub fold_log: usize,
}

impl Params {
    /// Kernel encoding with 32-byte salts, folding 4 variables between committed words.
    pub fn new(m: usize, log_inv_rate: usize, s: usize, queries: usize) -> Self {
        Params {
            basis: Basis::Kernel,
            m,
            log_inv_rate,
            s,
            queries,
            salt_len: 32,
            fold_log: 4,
        }
    }
    /// The committed levels j with their group sizes g: (0, g_0), (k, g_1), ..., covering the
    /// levels 0 .. s. For s = 0 the only group is (0, 1) (fibres, no fold).
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
    /// Classical parameters of Section 9 (use with `Fp2`): rate 1/4, final table of 16 elements
    /// (or fewer for m < 4), 148 queries, k = 4; soundness error below 2^-100.
    pub fn classical(m: usize) -> Self {
        Self::new(m, 2, m.saturating_sub(4), 148)
    }
    /// Post-quantum parameters of Remark 7.28 (use with `Fp4`): rate 1/4, 248 queries, k = 4.
    pub fn post_quantum(m: usize) -> Self {
        Self::new(m, 2, m.saturating_sub(4), 248)
    }
    /// Size M = 2^(m+R) of the evaluation domain.
    pub fn n(&self) -> usize {
        1 << (self.m + self.log_inv_rate)
    }
    fn omega(&self) -> Fp {
        Fp::two_adic_root((self.m + self.log_inv_rate) as u32)
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

/// The prover's state after `commit`: the table, the codeword w_0 and its salted tree.
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
}

/// Openings of one committed word: the distinct opened leaves in increasing order (their values
/// and salts) and the merged authentication paths.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LevelOpening<F> {
    pub values: Vec<Vec<F>>,
    pub salts: Vec<Vec<u8>>,
    pub nodes: Vec<Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof<E> {
    /// s_j(0), s_j(1), s_j(2) for j = 1 .. s
    pub sumcheck: Vec<[E; 3]>,
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

    /// Canonical encoding (the format of the test vectors): the s_j, the roots, the round salts,
    /// g, then for w_0 and each other committed word the opened leaves (values, then salt) and
    /// the merged path nodes. Field elements are little-endian u64 digits (e digits for E), with
    /// no length prefixes: all lengths are fixed by the parameters and the query points.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for h in &self.sumcheck {
            for x in h {
                x.to_bytes(&mut out);
            }
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

/// Commits to a table f over F_p of length 2^m: Enc(f) (kernel -> monomial transform with
/// (m/2)N additions, zero-padding, NTT of size M), and its salted Merkle tree over fibres. The
/// salts come from a fresh seed of the operating system.
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
    to_coefficients(p.basis, &mut w0);
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

/// Table -> monomial coefficients of the committed polynomial U.
pub fn to_coefficients<F: Field>(basis: Basis, v: &mut [F]) {
    match basis {
        Basis::Kernel => kernel_to_mono(v),
        Basis::Monomial => mobius(v),
    }
}

/// Kernel fold (Definition 5.5) in line form (Lemma 5.7):
///   fold_T(w)(x^2) = u + T v,  u = w_o - w_e,  v = 2 w_e - w_o,
///   w_e = (a+b)/2, w_o = (a-b)/(2x), a = w(x), b = w(-x).
/// Monomial baseline: classical FRI fold w_e + T w_o.
#[inline(always)]
fn fold_pair<E: ExtField>(basis: Basis, a: E, b: E, inv_2x: Fp, t: E, inv2: Fp) -> E {
    let we = (a + b) * inv2;
    let wo = (a - b) * inv_2x;
    match basis {
        Basis::Kernel => (wo - we) + t * (we.double() - wo),
        Basis::Monomial => we + t * wo,
    }
}

/// Folds a whole word on L_j to L_{j+1}.  inv_x0[k] = omega^{-k} for k < M/2 (level-0 table).
fn fold_word<F: Field, E: ExtField + From<F>>(
    basis: Basis,
    w: &[F],
    t: E,
    inv_x0: &[Fp],
    level: usize,
    inv2: Fp,
) -> Vec<E> {
    let h = w.len() / 2;
    crate::par::map_range(h, |i| {
        let inv_2x = inv_x0[i << level] * inv2;
        fold_pair(basis, E::from(w[i]), E::from(w[i + h]), inv_2x, t, inv2)
    })
}

/// s_j(0), s_j(1), s_j(2) from the current tables (parallel over blocks of pairs).
fn sumcheck_round<E: ExtField>(a: &[E], e: &[E]) -> [E; 3] {
    let pairs = a.len() / 2;
    let block = crate::par::GRAIN;
    let parts = crate::par::map_range(pairs.div_ceil(block), |c| {
        let mut h = [E::ZERO; 3];
        for i in c * block..((c + 1) * block).min(pairs) {
            let (a0, a1, e0, e1) = (a[2 * i], a[2 * i + 1], e[2 * i], e[2 * i + 1]);
            h[0] = h[0] + a0 * e0;
            h[1] = h[1] + a1 * e1;
            h[2] = h[2] + (a1.double() - a0) * (e1.double() - e0);
        }
        h
    });
    parts
        .iter()
        .fold([E::ZERO; 3], |s, h| [s[0] + h[0], s[1] + h[1], s[2] + h[2]])
}

fn eq1<E: ExtField>(a: E, c: E) -> E {
    a * c + (E::ONE - a) * (E::ONE - c)
}

/// h(T) from h(0), h(1), h(2).
fn interp3<E: ExtField>(h: &[E; 3], t: E) -> E {
    let one = E::ONE;
    let two = one.double();
    let inv2 = Fp::new(2).inv();
    let l0 = (t - one) * (t - two) * inv2;
    let l1 = -(t * (t - two));
    let l2 = t * (t - one) * inv2;
    l0 * h[0] + l1 * h[1] + l2 * h[2]
}

fn init_transcript<E: ExtField>(p: &Params, root: &Digest, z: &[E], v: E) -> Transcript {
    let mut tr = Transcript::new(LABEL);
    let params = [
        p.m as u64,
        p.log_inv_rate as u64,
        p.s as u64,
        p.queries as u64,
        (p.basis == Basis::Kernel) as u64,
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

/// Prover: returns the value v = f~(z) and the proof. The round salts and the salts of the trees
/// of w_1, ..., w_{s-1} come from a fresh seed of the operating system.
pub fn open<E: ExtField>(p: &Params, pd: &ProverData, z: &[E]) -> Result<(E, Proof<E>), Error> {
    open_inner(p, pd, z, &fresh_seed()?, None)
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

/// `cheat = Some(d)`: claim v + d instead of v, shift each s_j so that its sumcheck check passes,
/// fold honestly, and adjust the final table so that the closure check passes (used in tests).
fn open_inner<E: ExtField>(
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

    let mut a: Vec<E> = pd.table.iter().map(|&x| E::from(x)).collect();
    let mut e = eq_table(z);
    let mut v = a.iter().zip(&e).fold(E::ZERO, |s, (&x, &y)| s + x * y);
    if let Some(d) = cheat {
        v = v + d;
    }
    let mut claim = v;
    let mut tr = init_transcript(p, &pd.tree0.root(), z, v);

    let groups = p.groups();
    let committed = |j: usize| groups.iter().any(|&(l, _)| l == j);
    let group_of = |j: usize| groups.iter().find(|&&(l, _)| l == j).map_or(1, |&(_, g)| g);

    let mut sumcheck = Vec::with_capacity(p.s);
    let mut ts: Vec<E> = Vec::with_capacity(p.s);
    let mut roots = Vec::new();
    let mut round_salts = Vec::with_capacity(p.s + 1);
    let mut words: Vec<Vec<E>> = Vec::new(); // w_1 .. w_{s-1}
    let mut trees: Vec<(usize, MerkleTree)> = Vec::new(); // committed levels >= 1
    // Round j (1 <= j <= s): message s_j, then (j - 1 committed, j >= 2) the oracle w_{j-1};
    // challenge r_j.
    for j in 1..=p.s {
        let mut h = sumcheck_round(&a, &e);
        if cheat.is_some() {
            // shift every value of h by half the discrepancy: h(0) + h(1) then equals the claim
            let d = (claim - (h[0] + h[1])) * inv2;
            for x in h.iter_mut() {
                *x = *x + d;
            }
        }
        tr.absorb_field(b"sumcheck", &h);
        sumcheck.push(h);
        if j >= 2 {
            // w_{j-1} = fold_{r_{j-1}}(w_{j-2})
            let t = ts[j - 2];
            let next = if j == 2 {
                fold_word(p.basis, &pd.w0, t, &inv_x0, 0, inv2)
            } else {
                fold_word(p.basis, &words[j - 3], t, &inv_x0, j - 2, inv2)
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
        claim = interp3(&h, t);
        ts.push(t);
        a = restrict(&a, t);
        e = restrict(&e, t);
    }
    let mut g = a;
    if cheat.is_some() {
        // make the closure check pass by changing g(0)
        let prefix = ts
            .iter()
            .zip(z)
            .fold(E::ONE, |acc, (&t, &zj)| acc * eq1(t, zj));
        let e0 = prefix * eq_table(&z[p.s..])[0];
        let cur = prefix * mle_eval(&g, &z[p.s..]);
        g[0] = g[0] + (claim - cur) * e0.inv();
    }
    // Round s+1: message g; challenge: the query indices.
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
            sumcheck,
            roots,
            round_salts,
            g,
            level0,
            levels,
        },
    ))
}

/// The distinct leaves, in increasing order, opened at a committed word of length `len` with
/// group size 2^g: the query index i0 reads leaf i0 mod (len / 2^g).
fn positions(indices: &[usize], len: usize, g: usize) -> Vec<usize> {
    let leaves = len >> g;
    let mut pos: Vec<usize> = indices.iter().map(|&i| i % leaves).collect();
    pos.sort_unstable();
    pos.dedup();
    pos
}

/// The leaves opened in the commitment tree (fibres in coset order, group size 2^g0): for each
/// query index i0, the 2^(g0-1) consecutive leaves of the coset t = i0 mod (M / 2^g0).
fn level0_positions(indices: &[usize], n: usize, g0: usize) -> Vec<usize> {
    let mut pos: Vec<usize> = positions(indices, n, g0)
        .iter()
        .flat_map(|&t| (0..1usize << (g0 - 1)).map(move |u| (t << (g0 - 1)) + u))
        .collect();
    pos.sort_unstable();
    pos
}

fn open_level<F: Field>(w: &[F], tree: &MerkleTree, g: usize, pos: &[usize]) -> LevelOpening<F> {
    LevelOpening {
        values: pos.iter().map(|&t| leaf_values(w, g, t)).collect(),
        salts: pos.iter().map(|&t| tree.salt(t)).collect(),
        nodes: tree.multi_path(pos),
    }
}

/// Checks the shape and the merged openings of one committed word; returns nothing on success.
fn check_level<F: Field>(
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

/// Verifier: `Ok(())` if the proof is accepted; otherwise the reason for rejection. Never panics
/// on a malformed proof.
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
    if proof.sumcheck.len() != s
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

    // rounds 1 .. s
    let mut claim = v;
    let mut ts: Vec<E> = Vec::with_capacity(s);
    let mut next_root = 0;
    for j in 1..=s {
        let h = &proof.sumcheck[j - 1];
        if h[0] + h[1] != claim {
            return Err(Error::Check("sumcheck"));
        }
        tr.absorb_field(b"sumcheck", h);
        if j >= 2 && groups.iter().any(|&(l, _)| l == j - 1) {
            tr.absorb(b"root", &proof.roots[next_root]);
            next_root += 1;
        }
        tr.absorb(b"salt", &proof.round_salts[j - 1]);
        let t: E = tr.challenge();
        claim = interp3(h, t);
        ts.push(t);
    }
    // round s+1
    tr.absorb_field(b"final", &proof.g);
    tr.absorb(b"salt", &proof.round_salts[s]);
    let indices = tr.query_indices(p.queries, p.m + p.log_inv_rate);

    // closure
    let prefix = ts
        .iter()
        .zip(z)
        .fold(E::ONE, |acc, (&t, &zj)| acc * eq1(t, zj));
    if claim != prefix * mle_eval(&proof.g, &z[s..]) {
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

    // G in monomial form
    let mut gc = proof.g.clone();
    to_coefficients(p.basis, &mut gc);

    // For group (j, g) and fold step h: the inverse of a primitive 2^(g-h)-th root of unity,
    // zeta_h^{-1} = omega^{-M / 2^(g-h)}; the points of a coset at level j+h are
    // x_u = omega_{j+h}^t zeta_h^u.
    let leaf_of = |i: usize, t: usize| pos[i].binary_search(&t).expect("t is an opened leaf");
    for &i0 in &indices {
        if s == 0 {
            let t = i0 % (n / 2);
            let val = E::from(proof.level0.values[leaf_of(0, t)][i0 / (n / 2)]);
            if val != horner(&gc, E::from(omega.pow(i0 as u64))) {
                return Err(Error::Fold);
            }
            continue;
        }
        let mut carried: Option<E> = None;
        for (i, &(j, g)) in groups.iter().enumerate() {
            let mj = n >> j; // |L_j|
            let leaves = mj >> g;
            let t = i0 % leaves;
            let mut cur: Vec<E> = if i == 0 {
                // the coset t of w_0 from its 2^(g0-1) fibres: entry u lies in fibre u mod
                // 2^(g0-1), first value for u < 2^(g0-1) and second value otherwise
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
                // the value of w_j at the query point, computed from the previous group
                if cur[(i0 % mj) / leaves] != c {
                    return Err(Error::Fold);
                }
            }
            // fold g times: at step h the entries are w_{j+h} at t + u * leaves
            let mut x_inv = omega_inv.pow((t as u64) << j); // omega_j^{-t}
            for h in 0..g {
                let half = cur.len() / 2;
                let zeta_inv = omega_inv.pow((n >> (g - h)) as u64);
                let mut xu_inv = x_inv;
                let mut next = Vec::with_capacity(half);
                for u in 0..half {
                    let inv_2x = xu_inv * inv2;
                    next.push(fold_pair(
                        p.basis,
                        cur[u],
                        cur[u + half],
                        inv_2x,
                        ts[j + h],
                        inv2,
                    ));
                    xu_inv = xu_inv * zeta_inv;
                }
                cur = next;
                x_inv = x_inv * x_inv;
            }
            carried = Some(cur[0]);
        }
        // w_s at the query point, against G
        let y = omega.pow(((i0 % (n >> s)) as u64) << s); // omega_s^{i0 mod M_s}
        if carried != Some(horner(&gc, E::from(y))) {
            return Err(Error::Fold);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{Fp2, Fp4};

    fn cheater_rejected<E: ExtField>(mk: impl Fn(Fp, Fp) -> E) {
        // Commits Enc(f) honestly, claims v + 1, keeps every sumcheck check and the closure check
        // satisfied. Theorem 7.13 (case 2) predicts rejection; it happens in the query phase.
        let mut x = 99u64;
        let mut rnd = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            Fp::new(x)
        };
        for (m, s, k) in [(6, 3, 1), (8, 5, 2), (8, 8, 4), (10, 6, 3), (10, 9, 4)] {
            for basis in [Basis::Kernel, Basis::Monomial] {
                let p = Params {
                    basis,
                    m,
                    log_inv_rate: 2,
                    s,
                    queries: 20,
                    salt_len: 32,
                    fold_log: k,
                };
                let table: Vec<Fp> = (0..1 << m).map(|_| rnd()).collect();
                let z: Vec<E> = (0..m).map(|_| mk(rnd(), rnd())).collect();
                let (root, pd) = commit(&p, &table).unwrap();
                let (v, proof) = open_inner(&p, &pd, &z, &[3u8; 32], Some(E::ONE)).unwrap();
                assert_eq!(
                    verify(&p, &root, &z, v, &proof),
                    Err(Error::Fold),
                    "m={m} s={s}"
                );
                // sanity: the honest proof for the same data is accepted
                let (v, proof) = open(&p, &pd, &z).unwrap();
                assert_eq!(verify(&p, &root, &z, v, &proof), Ok(()));
            }
        }
    }

    #[test]
    fn consistent_sumcheck_cheater_is_rejected() {
        cheater_rejected(Fp2);
        cheater_rejected(|a, b| Fp4(Fp2(a, b), Fp2(b, a)));
    }
}
