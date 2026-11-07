# Chapter 1 mathematical theorem ledger

**Paper proof** means that the complete proof is in \`sections/01-introduction.tex\`. This does not assert that the new manuscript has yet been certified in Lean 4. Parent-KBFold already formalizes much of the pre-existing algebra in \`lean/KBFold/Kernel.lean\`.

| Result | Paper proof | Dependencies | Proposed Lean target |
|---|---|---|---|
| Degree and monic kernel | included | Kernel definition | \`kernel_monic_degree\` |
| Even/odd kernel recursion | included | Indexing | \`kernel_bit_recursion\` |
| Unique even/odd decomposition | included | Polynomial coefficients | \`poly_even_odd_unique\` |
| Kernel basis theorem | included | Recursion, decomposition, induction | \`kernel_basis\` |
| Highest coefficient identity | included | Degree and monicity | \`kernel_top_coeff\` |
| Boolean interpolation | included | Equality weights | \`eq_weight_bool\` |
| Multilinear restriction | included | Equality weights | \`mle_restrict_first\` |
| Fold dictionary | included | Recursion and decomposition | \`kernel_fold_dictionary\` |
| Iterated folds | included | Restriction and fold dictionary | \`kernel_fold_iterate\` |
| Unmasked sumcheck witness dependence | included | One-variable MLE | \`sumcheck_message_witness_dependent\` |
| Kernel masking linearity | included | Fold dictionary | \`kernel_mask_linear\` |
| Binary-field evaluation basis | included | Basis theorem, minimal polynomial | \`kernel_eval_basis_binary\` |
| Masked transposition as kernel fold | included | Coordinate extraction | \`delta_eq_kernel_fold\` |
| Characteristic-dependent partition | included | Distributivity | \`kernel_sum_product\` |
| Binary multilinearization of kernel | included | Explicit monomial expansion | \`multilinearize_kernel\` |
| Complete fold/multilinearization identity | included | Kernel expansion, linearity | \`kernel_fold_eq_multilinear_eval\` |

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
