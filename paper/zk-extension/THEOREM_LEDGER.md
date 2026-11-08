# Chapter 1 mathematical theorem ledger

**Paper proof** means that the complete proof is in `sections/01-introduction.tex`. This does not assert that the new manuscript has yet been certified in Lean 4. Parent-KBFold already formalizes much of the pre-existing algebra in `lean/KBFold/Kernel.lean`.

| Result | Paper proof | Dependencies | Proposed Lean target |
|---|---|---|---|
| Degree and monic kernel | included | Kernel definition | `kernel_monic_degree` |
| Even/odd kernel recursion | included | Indexing | `kernel_bit_recursion` |
| Unique even/odd decomposition | included | Polynomial coefficients | `poly_even_odd_unique` |
| Kernel basis theorem | included | Recursion, decomposition, induction | `kernel_basis` |
| Highest coefficient identity | included | Degree and monicity | `kernel_top_coeff` |
| Boolean interpolation | included | Equality weights | `eq_weight_bool` |
| Multilinear restriction | included | Equality weights | `mle_restrict_first` |
| Fold dictionary | included | Recursion and decomposition | `kernel_fold_dictionary` |
| Iterated folds | included | Restriction and fold dictionary | `kernel_fold_iterate` |
| Unmasked sumcheck witness dependence | included | One-variable MLE | `sumcheck_message_witness_dependent` |
| Kernel masking linearity | included | Fold dictionary | `kernel_mask_linear` |
| Binary-field evaluation basis | included | Basis theorem, minimal polynomial | `kernel_eval_basis_binary` |
| Masked transposition as kernel fold | included | Coordinate extraction | `delta_eq_kernel_fold` |
| Characteristic-dependent partition | included | Distributivity | `kernel_sum_product` |
| Binary multilinearization of kernel | included | Explicit monomial expansion | `multilinearize_kernel` |
| Complete fold/multilinearization identity | included | Kernel expansion, linearity | `kernel_fold_eq_multilinear_eval` |

## Separation of settings

- **Base KBFold**: odd-characteristic polynomial fold, smooth multiplicative domain, sumcheck, query openings.
- **Ring switching**: binary extension field, trace-dual coordinates, masked correction.
- **Zero-knowledge KBFold**: complete simulator and masked transcript analysis; no theorem is implicitly imported from binary characteristic into odd characteristic.

## External mathematical input

- Original KBFold proof system, source in the parent repository.
- Existence of a trace-dual basis for finite separable extensions, formally treated in Chapter 7.
- Formal cryptographic definitions and interfaces, to be introduced in Chapter 3.


## Chapter 2: Historical Background and Related Work

Each theorem marked **full** has a complete proof in the manuscript. No new Lean declaration is yet certified.

| Result | Proof | Dependencies | Proposed Lean declaration |
|---|---|---|---|
| Sumcheck partial-sum telescoping | full | finite sums | sumcheck_partial_telescope |
| Sumcheck completeness | full | telescoping | sumcheck_complete |
| Polynomial root bound | full | field root count | sumcheck_poly_root_bound |
| Sumcheck soundness | full | root bound, timing | sumcheck_sound |
| Uniform additive masking | full | translation of finite vector spaces | uniform_additive_mask |
| Zero-sum polynomial masks | full | linear functional kernel | zero_sum_mask |
| Explicit zero-sum polynomial | full | Boolean partition | zero_sum_explicit |
| First-round masking linearity | full | finite-sum distribution | partial_sum_additive |
| Two-element square fibers | full | characteristic not two | square_fiber_pair |
| Word-fold consistency | full | even/odd decomposition | word_fold_eval_compat |
| Reed--Solomon folded degree | full | degree bound | fold_rs_mem |
| Even-power shift | full | exponent parity | pfold_even_power_shift |
| High-degree mask propagation | full | induction and shift | high_mask_fold_iterate |
| Masked KBFold decomposition | full | fold dictionary | masked_kernel_fold_iterate |
| Binary transposition involution | full | coordinate uniqueness | binary_transpose_involutive |
| Packed transposition identity | full | coordinate linearity | packed_transpose_identity |
| Ring-switching batching soundness | full | Schwartz--Zippel | ring_switch_batch_sound |
| Mask additivity | full | coordinate linearity | masked_transpose_add |
| Trace properties and surjectivity | full | finite-field Frobenius | absolute_trace_surjective |
| Artin--Schreier characterization | full | trace and cardinality | artin_schreier_uniform |
| Frobenius decomposition | full | trace expansion | delta_frobenius_decomp |
| Backward recurrence | full | telescoping in characteristic two | frobenius_backward_recurrence |
| Affine masked recurrence | full | backward recurrence | masked_recurrence_affine |
| Kernel correction | full | Chapter 1 kernel fold | delta_eq_kernel_fold |
| Structural separation | full | basis uniqueness | kernel_correction_structural |

### Historical provenance

- LFKN, FRI, BaseFold, Libra: primary historical works cited; full cryptographic theorems are not re-proved.
- Diamond--Posen: transposition identity and random-batching bound rederived algebraically.
- Kochergin: Frobenius recurrence derived; full IOP ZK theorem is externally sourced.
- Frigo--shelat: trace-zero algebra derived; general arbitrary bit-linear claim reduction is cited.
- KBFold: existing kernel-folding dictionary, proof repeated where necessary.

### New algebraic bridge

For a high-degree mask in the original KBFold setting, the chapter proves

    pfold^j(X^N R) = X^(N/2^j) R_j,  N = 2^m,  0 <= j <= m.

This exact identity is the starting point for analyzing the enlarged Reed--Solomon degree, masked final closure, and subsequent oracle simulation.


### Chapter 2 audit additions

| Result | Proof | Proposed Lean declaration |
|---|---|---|
| Univariate polynomial root-count lemma | full induction | polynomial_card_roots |
| Multivariate Schwartz--Zippel | full induction on the number of variables | mvpoly_schwartz_zippel |
| Trace-dual basis existence and uniqueness | full finite-dimensional linear-algebra proof | trace_dual_basis_exists_unique |


## Chapter 3: Formal Security Model

**Complete source:** `sections/03-security.tex` (seven subsections).
**Detailed map:** [CHAPTER_03_LEAN_MAP.md](CHAPTER_03_LEAN_MAP.md), which lists **62 individually labeled definitions/results**, including **32 complete paper proofs**.
**Certification status:** LaTeX proof, not yet Lean-certified. Existing KBFold foundational results are linked but never counted as new Lean certification.

### Principal proved results

- Total variation triangle, event characterization, data processing, and a stepwise hybrid lemma.
- Finite typed oracle transcript and adaptive decision-tree model.
- Reed--Solomon distance \(M-N+1\), uniqueness for \(2\tau<M-N+1\).
- Round-by-round soundness and knowledge-extraction implication.
- Statistical simulator definition, its two-witness consequence, and the one-query leakage theorem for an unmasked KBFold oracle.
- Exact linear-mask coset criterion, uniform conditional masks after adaptive reads, and interpolation for \(Q\) evaluation queries.
- Online commitment-before-point simulation target and a counterexample showing \(U_f+X^N R\) cannot retain the original constant final closure check.

### Not yet established

- An explicit masking distribution for all **odd-characteristic** KBFold messages.
- Online ZK simulator for all committed-fold word openings, round polynomials and final table.
- Soundness of the enlarged-degree code under revised closure checks.
- QROM/Fiat--Shamir zero-knowledge compilation.


## Chapter 4 — Boolean-Kernel Basis: Complete Algebraic Theory

- 63 formally numbered definitions/results; independent small proofs throughout.
- Complete map: [CHAPTER_04_LEAN_MAP.md](CHAPTER_04_LEAN_MAP.md).
- Proven algebraic content: coefficient expansion; tensor basis; inverse Möbius transform; low-degree characterization; evaluation curve; weighted complete fold; characteristic-two specialization; fold reparametrization; high-degree mask degree; bounded-query mask hiding for a single oracle.
- No new Lean proof has been checked in this chapter.
- Original KBFold kernel algebra was previously proved; this manuscript rederives it self-containedly before the new masking-specific consequences.

- Chapter 4 tradeoff theorem: a uniform degree-<2^t mask hides up to 2^t adaptive queries to one nonzero-point oracle, while increasing the Reed--Solomon degree limit from N to N+2^t; exact distance and unique-radius bounds follow.


## Chapter 5: Multilinearization, Folding, and Masks

**Source:** `sections/05-folding.tex` with seven small subsections.
**Lean map:** [CHAPTER_05_LEAN_MAP.md](CHAPTER_05_LEAN_MAP.md).
**Audit:** 64 individually labeled definitions/results; 51 complete paper proofs. New Chapter 5 declarations are **not yet checked in Lean**.

Main proved algebraic statements:

- Prefix restriction and multilinear evaluation, with complete finite-sum reindexing.
- Global normalized polynomial fold on monomials; tensor form valid in every field.
- Characteristic-two specialization and explicit odd-characteristic counterexample.
- Kernel polynomial/table restriction commutative diagram at every fold depth.
- Direct-sum high-degree masked encoding `(f,R) ↦ U_f+X^N R`.
- Full masked fold invariant and degree budget `D_j=N/2^j+ceil(B/2^j)`.
- **Linear final closure** `Q_m=MLE(f)(r)+rho_r(R) X` for `1≤B≤N`.
- Exact enlarged-degree RS codeword folding and rate transition for `B=2^t`.
- Local residual root count and two-point constant-term check for a degree-<2 final polynomial.
- Exact fixed-schedule joint masking criterion via the image of a finite-field linear map.
- Explicit one-query attack showing that disclosure of the final mask slope can cancel a degree-zero mask from an earlier oracle opening, even when both messages are individually uniform.

**Security boundary:** The chapter does not prove that a malicious oracle lies near the enlarged RS code, nor the joint authenticated online ZK simulator. Those are new protocol theorems, not consequences of the algebraic identities.


## Chapter 6 — Characteristic-Two Specializations

**Source:** `sections/06-binary.tex` and eight proof-oriented subsections.
**Lean map:** [CHAPTER_06_LEAN_MAP.md](CHAPTER_06_LEAN_MAP.md).
**Audit:** 85 separately labeled statements, including **67 full paper proofs** and 18 typed definitions. The new Chapter 6 results are **not yet Lean-certified**.

### Proven algebraic results

- Characteristic-two Frobenius on scalars and polynomial coefficients, including field and kernel covariance.
- The partition identity `sum_b K_b(X)=1`, and complete/partial multilinearization by explicit monomial expansion.
- Absolute trace and Artin--Schreier: `im(t²+t)=ker(Tr)`, uniform trace-zero masking.
- Existence of a full-degree field element, a kernel evaluation basis and its trace-dual coordinate basis.
- Exact affine kernel-correction identity `Tr(V_k)=coord_k(D_c+Delta_p)`.
- Uniformity of independently masked public trace-zero messages for a fixed consistent instance.
- Unanchored residual collision and construction of the minimal-degree anchored family `{1,W_b}`.
- Root bound `n/2^n` for a fixed nonzero anchored residual.
- Perfect algebraic completeness and two-challenge **coefficient-consistency** bound `(ell+n)/2^n` for fixed `p,c` before `theta`, with all residuals fixed before `z`.
- Proof that a binary field has no even-order multiplicative subgroup, so KBFold's original odd-characteristic `±x` word fold does not directly carry over.

### Security boundary

The chapter proves *an algebraic consistency checker*, **not** zero knowledge for the entire Ring Switching protocol or the odd-characteristic KBFold PCS. In particular it does not establish the joint distribution of the public vector `U` together with the later scalar `A`, a hiding authenticated commitment, or a full online simulator.

### Reproducible audit

Run `sh audit/RUN.sh` to execute the existing kernel tests plus the new deterministic GF(16) and GF(256) tests covering basis, trace duality, affine equations, honest checks and anchored root counts. These tests supplement the full mathematical proofs.


## Chapter 7 — Binary-Field Packing and Transposition

**Source:** `sections/07-packing.tex` with seven proof-oriented subsections.
**Lean map:** [CHAPTER_07_LEAN_MAP.md](CHAPTER_07_LEAN_MAP.md).
**Audit:** 71 labeled definitions/results: 22 definitions and **49 complete paper proofs**. None of these Chapter 7 declarations has yet been machine checked in Lean 4.

### Established mathematical results

- Lossless $\F_2$-basis packing, inverse extraction, bit-column identities, and original two-axis multilinear evaluation.
- Exact coordinate-matrix transpose, involution $\mathcal T^2=\mathrm{id}$, proof of $\F_2$-linearity, and proof that it is not $L$-linear for $n>1$.
- Packed transposition identity $\mathcal T(s^*)_u=\sum_jd_u(h_j)\widehat w_j$, random batching $B_{s^*}=\sum_j a_j\widehat w_j$, and a degree-$\ell$ discrepancy test.
- Independent uniform pads $p,p_{\mathrm{in}}$, uniform public $(m,y')$, pad correction $C_p$, and complete IN/OUT/CLAIM affine equations.
- Error decomposition $\mathsf{OUT\ residual}=B_{m+s^*+p}+D_{c+c^p}$, exact honest completeness and conditional algebraic soundness at most $(\ell+n)/2^n$ against false evaluation claims.
- Trace-dual field-affine implementation interface and an explicit proof that exposing $(m,c^p)$ recovers $s^*$.
- An ideal-to-implementation soundness union bound, conditional on independently proving external commitment/affine-proof failures.

**Open:** External PCS soundness, binding to packed bits, authenticated openings, joint online simulator for $m,y',U,A$, and application to the odd-characteristic KBFold IOP.

**Reproducibility:** Chapter 7 Rust tests exercise packed Ring Switching identities and masking over GF(16) and GF(256).


## Chapter 8 — Original Diamond--Posen Tensor Ring-Switching Compiler

**Source:** `sections/08-diamond-posen.tex` and seven detailed subsections.
**Lean map:** [CHAPTER_08_LEAN_MAP.md](CHAPTER_08_LEAN_MAP.md).
**Paper audit:** 56 labeled definitions/results and **41 complete proofs**. None of the new Chapter 8 declarations has yet been Lean-certified.

### Mathematical results proved in this chapter

- Tensor algebra $A=L\otimes_{\F_2}L$, commuting embeddings $\varphi_0,\varphi_1$, explicit left-$L$ column coordinates and contraction.
- Identity $\operatorname{Col}(\varphi_1(T')(\varphi_0(r_{\rm hi})))_v=s_v^*$ and $y_w=C_q(S)$, without replacing the tensor by ordinary field multiplication.
- Degree-two tensor-valued sumcheck summand $H$ and exact Boolean-sum relation $\sum_b H(b)=S$.
- Ring root-count lemma: a nonzero polynomial of degree at most $d$ has at most $d$ roots among values $\varphi_1(z)$, $z\in L$, because their pairwise differences are units in $A$.
- Causal degree-two sumcheck with algebraic soundness at most $2h/|L|$.
- Faithful Construction 4.1 reduction to a bound committed large-field multilinear polynomial, perfect completeness, and conditional false-claim soundness at most $2h/|L|+\varepsilon_{\mathrm{eval}}$.
- Explicit privacy obstruction: the unmasked $A$-valued initial message reveals every partial evaluation; two equal-evaluation witnesses can be perfectly distinguished by one tensor column.
- Strict separation from the masked kernel-coordinate checker of Chapters 6--7 and its still-unproved online zero-knowledge simulator.

**Important attribution:** Diamond and Posen (ePrint 2024/504, §4) introduced this original tensor-algebra compiler; its reconstruction is not claimed as our novel result. The later mask techniques of Kochergin and Frigo--shelat are cited independently.

**Rust audit:** GF(16)/GF(256) tests for tensor multiplication, embeddings, exact columns, original evaluation, terminal factor and the embedded-field polynomial root bound.


## Chapter 9 — Zero-Knowledge Ring Switching

**Source:** `sections/09-zk-ring-switching.tex`, seven subsections.
**Lean map:** [CHAPTER_09_LEAN_MAP.md](CHAPTER_09_LEAN_MAP.md).
**Proof audit:** 51 labeled definitions/results and **37 complete mathematical proofs**. The newly proposed Lean 4 declarations have not been certified.

### Proved facts

- Exact causal one-opening public-core simulation: the joint view `(m,y',theta,U,z,A)` is independent of an admissible witness, even under adaptively chosen verifier challenges, provided fresh independent field masks are used.
- Uniform input pair `(m,y')`, uniform conditional trace-zero vector `U`, and uniform conditional final field scalar `A`.
- Exact conditional Artin--Schreier mask fibers (two preimages per coordinate), and existence/count of hidden witness completions.
- Every enforced hidden-field consistency relation is affine after public challenges; the public check uses `Tr(U_k)=0`. Hidden quadratic `sigma=rho²` is tested probabilistically through anchored residuals rather than directly proved.
- Nonzero residual root error at most `n/|L|`; ideal false-claim soundness at most `(ell+n)/|L|` with all commitment/challenge timing explicit.
- A two-opening pad-reuse attack distinguishing equal-authorized-evaluation witnesses with statistical distance one.
- Perfect complete-view privacy in a deliberately **opaque ideal proof functionality**, plus a conditional real-world ZK composition theorem assuming a separate full commitment/proof/authenticated-opening simulator.
- Exact single-opening message and auxiliary-state counts and the characteristic-two versus existing odd-characteristic KBFold obstacle.

**Security boundary:** Chapter 9 does **not** establish unconditional real-world zero knowledge for the complete KBFold PCS. Concrete binding, hiding, online simulation of all commitment roots/proofs/openings, and the original KBFold degree/proximity arguments remain to be proved.

**Reproducible tests:** Chapter 9 has deterministic finite-field regression tests of public message distributions and conditional mask laws over GF(4) and GF(16).


## Chapter 10 — Commitment and Affine-Proof Realization

**Source:** `sections/10-commitment-realization.tex` and eight small sections.
**Lean map:** [CHAPTER_10_LEAN_MAP.md](CHAPTER_10_LEAN_MAP.md).
**Audit:** 57 labeled definitions/results, with **39 complete mathematical paper proofs**. No new Chapter 10 theorem has yet been Lean certified.

### Established mathematics

- Exact compilation of public-coefficient affine constraints over `GF(2^n)` into parity constraints over their `n` binary coordinates.
- Concrete fresh Pedersen commitments `C=g^b h^r`: perfect hiding and computational binding with explicit discrete-log extraction from two inconsistent openings.
- Full Schnorr OR proof equations, perfect completeness, exact honest-verifier zero-knowledge simulator and special-soundness extraction.
- Integer-lift parity OR proof that correctly handles `1+1=0` in `GF(2)` without falsely treating odd-prime-order Pedersen commitments as XOR-homomorphic.
- Compilation of all Chapter 9 affine equations and binary packing links into committed parity checks.
- **Perfect honest-sigma-verifier transcript simulation** for one admissible opening, with potentially adaptive outer Ring Switching challenges.
- A conditional false-claim soundness bound `(ell+n)/2^n + eps_ext + eps_DL`, requiring a separate **early-extraction and challenge-timing contract** for the actual adaptive proof composition.
- Cost bounds establishing that the raw construction is neither succinct nor post-quantum.

### Security boundary

This is a **classical, honest-sigma-verifier** construction, not a complete malicious-verifier, QROM or post-quantum KBFold PCS theorem. It does not simulate original KBFold commitment roots, Merkle authentication paths or folded oracles. The multistage extraction contract is stated precisely but **has not been discharged** by the current component proofs.

### Reproducible audit

`audit/affine_sigma.rs` uses an intentionally insecure tiny group and GF(16) only for checking algebra, OR transcript distributions, special-soundness formulas, and field-to-parity identities; it is not a cryptographic implementation.


## Chapter 11 — Malicious-Verifier Zero Knowledge and Temporal Extraction

**Source:** `sections/11-malicious-verifier.tex` and eight proof-oriented subsections.
**Lean map:** [CHAPTER_11_LEAN_MAP.md](CHAPTER_11_LEAN_MAP.md).
**Audit:** 56 individually labeled statements, including **40 complete mathematical proofs** and 16 definitions. New Chapter 11 declarations are not yet machine-checked in Lean.

### Proved

- Exact fixed-bit Schnorr OR proof simulation, including the uniform first-message law.
- A balanced classical rewinding simulator for an arbitrary challenge-selecting or aborting verifier, with **perfect transcript law** and **two expected trials** per mini-proof.
- Sequential one-bit repetition yields perfect expected-time **malicious-verifier zero knowledge for the one-opening binary-field affine transcript**, including the public core and Pedersen commitment proofs, while allowing adaptive outer Ring Switching challenges.
- The bounded-retry simulator runs in strict polynomial time with statistical error at most `M*2^(-R)`.
- Exact two-run forking probability `p*(p-2^(-kappa))` for a deterministic reset prover and lower bound `eps*(eps-2^(-kappa))` for a randomized prover, with extraction from the earliest distinct challenge bit.
- Stand-alone extraction before each outer challenge when the relevant bitness proof is completed before that challenge.
- False-parity discrete-log reduction and `eps <= 2^(-kappa)+sqrt(delta_DL)` for a fixed aggregate with known true bit openings.
- A conditional outer false-claim soundness theorem with explicit global extraction, row proof and authenticated-oracle error terms.

### Open and excluded

**Global multistage temporal extraction has not been proved.** The two-run local witness extractor does not yet guarantee a consistent extraction of all dependent field variables on one accepted transcript while preserving challenge independence. The proof does not cover original KBFold authentication paths, odd-characteristic folding, multiple openings, quantum verifiers or QROM soundness. The bit-commitment compiler remains nonsuccinct and classical.

### Rust verification

`audit/malicious_sigma.rs` exhaustively enumerates tiny-group Schnorr OR transcript distributions, a malicious verifier's adaptive challenge/abort behavior, and challenge-tree forking and extraction. The tiny group is for algebraic regression testing only, not cryptographic deployment.


## Chapter 12 — Global Temporal Extraction and Classical Soundness

**Source:** `sections/12-global-extraction.tex` (five detailed subsections).
**Lean map:** [CHAPTER_12_LEAN_MAP.md](CHAPTER_12_LEAN_MAP.md).
**Fixed roadmap:** [ROADMAP_LOCK.md](ROADMAP_LOCK.md) — Chapters **12–15 only**, no additional chapters.
**Audit:** 32 labeled statements: 11 definitions and **21 complete mathematical proofs**, with no new Lean-certified declaration yet.

### Main theorem

A classical checkpoint/replay extractor follows **one unchanged accepted main transcript**, and privately searches for a second accepted challenge string at each of at most `J` sequential OR proof blocks with `kappa` one-bit challenges. For at most `R` side attempts per block:

```
Pr[main accepts AND any OR opening missing]
    <= J * (2^(-kappa) + 1/(R+1)).
```

It fixes one canonical bit-commitment registry before `theta` and the new auxiliary variables before `z`; conflicting valid openings compute the forbidden Pedersen setup discrete logarithm. It preserves **the exact original main transcript** and fresh independent outer challenges. This replaces the formerly unspecified global temporal extractor for the **classical sequential OR affine component**.

Consequently, under the separate authenticated-oracle error `eps_oracle`,

```
Pr[false evaluation claim accepted]
    <= (ell+n)/2^n + eps_oracle + Adv_DL(D_R)
       + J*(2^(-kappa) + 1/(R+1)).
```

If an attacker has non-negligible success, choosing a polynomial replay budget inverse in that success yields a non-negligible discrete-log reduction whenever the three baseline errors are negligible.

**Exact boundary:** This does not implement or prove authentication/zero knowledge for the original KBFold folded polynomial oracle, Merkle/FRI openings or odd-characteristic PCS; those belong strictly to Chapters 13–14. Quantum rewinding and post-quantum commitments are also excluded.

**Regression audit:** `audit/global_extraction.rs` verifies the combinatorial replay bound in exact integer arithmetic, exhaustively checks small challenge trees and tests commitment collision recovery.


## Chapter 13 — Complete Masked KBFold Protocol and Authenticated Oracles

**Source:** `sections/13-complete-masked-kbfold.tex` (six proof-oriented subsections).
**Lean map:** [CHAPTER_13_LEAN_MAP.md](CHAPTER_13_LEAN_MAP.md).
**Locked roadmap:** [ROADMAP_LOCK.md](ROADMAP_LOCK.md).
**Proof audit:** 47 labeled definitions/results and **28 complete mathematical paper proofs**. No new Chapter 13 Lean declaration is machine-certified.

### Completed construction

- Original **odd-characteristic KBFold** field, high-degree masked polynomial $Q_0=U_f+X^NR$, normalized fold chain and precise enlarged RS degree budgets $D_j$.
- Authenticated folded words with **fresh perfectly hiding Pedersen bit-commitment leaves**. Public Merkle roots, leaf commitments and paths reveal no raw field symbols; hidden circuit proofs check the openings.
- A full concealed Sumcheck with $\\mu_j(T)=s_j(T)+b_{j-1}/2+c_j(2T-1)$, hidden coefficient/offset commitments, exact endpoint/challenge equations and the last-round relation $\\mu_m(r_{m-1})=\\chi_m[X^0]Q_m+b_m$.
- Complete interactive prover/verifier with pre-evaluation registration, pre- and post-challenge field relations, adaptive local fold queries, and two-point final linear closure.
- **Perfect algebraic completeness** relative to a perfectly complete relation-proof engine.
- An exact **online simulator for the complete public authentication shell** (commitments, Merkle roots, paths, queries), publishing the initial root **before** the evaluation point; a conditional theorem for the full view including proof transcripts.
- A conditional full-relation soundness theorem with explicit preprocessing-extraction, relation-soundness, Pedersen-binding and Merkle-collision errors.

### Strict separation of the two verification modes

**Full-relation mode** is a completely specified, but nonsuccinct, polynomial-size NP circuit proof of every committed word. Its security still depends on the selected relation engine's actual online ZK and knowledge-extraction reductions.

**Sparse KBFold mode** retains local queries and can hope for succinctness; soundness against arbitrary adversarial non-codewords with revised RS rates $D_j/M_j$ has **not** been proved by the algebraic fold identities. This is a named Chapter 14 obligation.

The ordinary binary-field affine proof from Chapters 10–12 does **not** automatically certify odd-field multiplication, hash arithmetic or NP circuit proof security. Classical, ROM and quantum/QROM cases remain separate.

### Tests and deliverables

`audit/full_kbfold.rs` runs deterministic finite-field checks of masked Sumcheck offsets, codeword folds, final closure, and hiding distributions for small pedagogical prime groups; the full manuscript is built by GitHub CI.
