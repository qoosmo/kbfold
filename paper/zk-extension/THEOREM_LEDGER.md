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
