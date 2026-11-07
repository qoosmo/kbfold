# Chapter 4 — Lean 4 theorem map

**Statements:** 63 labeled definitions, lemmas, propositions, theorems and corollaries.

**Status:** Complete paper proofs for all results; no claim of new Lean certification. The original KBFold Lean project already proves overlapping base-algebra results.

| Subsection | Type | Statement | LaTeX label | Proposed Lean declaration |
|---|---|---|---|---|
| 04a-indexing-coefficients | definition | Bit sets and binary exponents | `def:kbalgebra:bits` | `KBFold.ZKKernel.bits` |
| 04a-indexing-coefficients | lemma | Binary-subset bijection | `lem:kbalgebra:binary-bijection` | `KBFold.ZKKernel.binary_bijection` |
| 04a-indexing-coefficients | definition | General kernel and Boolean kernel | `def:kbalgebra:kernel` | `KBFold.ZKKernel.kernel` |
| 04a-indexing-coefficients | lemma | Explicit product expansion | `lem:kbalgebra:product-expansion` | `KBFold.ZKKernel.product_expansion` |
| 04a-indexing-coefficients | lemma | Coefficient formula | `lem:kbalgebra:coefficient-rule` | `KBFold.ZKKernel.coefficient_rule` |
| 04a-indexing-coefficients | corollary | Degree, leading term, and constant term | `cor:kbalgebra:monic` | `KBFold.ZKKernel.monic` |
| 04a-indexing-coefficients | lemma | Block factorization | `lem:kbalgebra:block` | `KBFold.ZKKernel.block` |
| 04a-indexing-coefficients | corollary | Lowest-bit kernel recursion | `cor:kbalgebra:recursion` | `KBFold.ZKKernel.recursion` |
| 04b-kronecker | definition | Coefficient vectors and kernel coordinates | `def:kbalgebra:coords` | `KBFold.ZKKernel.coords` |
| 04b-kronecker | definition | Bitwise tensor product of matrices | `def:kbalgebra:tensor` | `KBFold.ZKKernel.tensor` |
| 04b-kronecker | lemma | Tensor multiplication rule | `lem:kbalgebra:mixed-product` | `KBFold.ZKKernel.mixed_product` |
| 04b-kronecker | lemma | One-bit coefficient transform | `lem:kbalgebra:one-bit` | `KBFold.ZKKernel.one_bit` |
| 04b-kronecker | proposition | Kronecker coefficient matrix | `prop:kbalgebra:kronecker` | `KBFold.ZKKernel.kronecker` |
| 04b-kronecker | theorem | Boolean-kernel basis and inverse transform | `thm:kbalgebra:basis` | `KBFold.ZKKernel.basis` |
| 04b-kronecker | corollary | Unique kernel coordinates | `cor:kbalgebra:unique-coordinates` | `KBFold.ZKKernel.unique_coordinates` |
| 04c-transforms | lemma | Forward transform in subset form | `lem:kbalgebra:forward` | `KBFold.ZKKernel.forward` |
| 04c-transforms | lemma | Monomial expansion in the kernel basis | `lem:kbalgebra:monomial-inverse` | `KBFold.ZKKernel.monomial_inverse` |
| 04c-transforms | proposition | Inverse M\"obius formula | `prop:kbalgebra:inverse` | `KBFold.ZKKernel.inverse` |
| 04c-transforms | lemma | One-coordinate transform algorithms | `lem:kbalgebra:pair-algorithm` | `KBFold.ZKKernel.pair_algorithm` |
| 04c-transforms | corollary | Exact transform cost | `cor:kbalgebra:transform-cost` | `KBFold.ZKKernel.transform_cost` |
| 04c-transforms | corollary | Highest and constant coefficients | `cor:kbalgebra:extreme-coeffs` | `KBFold.ZKKernel.extreme_coeffs` |
| 04c-transforms | proposition | Kernel coordinates of a constant | `prop:kbalgebra:constant` | `KBFold.ZKKernel.constant` |
| 04c-transforms | proposition | Kernel partition product | `prop:kbalgebra:partition` | `KBFold.ZKKernel.partition` |
| 04d-low-degree | definition | Coefficient blocks | `def:kbalgebra:blocks` | `KBFold.ZKKernel.blocks` |
| 04d-low-degree | lemma | Existence and uniqueness of coefficient blocks | `lem:kbalgebra:block-unique` | `KBFold.ZKKernel.block_unique` |
| 04d-low-degree | lemma | Block degree criterion | `lem:kbalgebra:degree-blocks` | `KBFold.ZKKernel.degree_blocks` |
| 04d-low-degree | definition | High-bit kernel polynomials | `def:kbalgebra:high-block` | `KBFold.ZKKernel.high_block` |
| 04d-low-degree | lemma | Kernel blocks equal monomial blocks | `lem:kbalgebra:kernel-block-decomposition` | `KBFold.ZKKernel.kernel_block_decomposition` |
| 04d-low-degree | lemma | Low degree iff each high kernel polynomial is constant | `lem:kbalgebra:high-constant` | `KBFold.ZKKernel.high_constant` |
| 04d-low-degree | theorem | Complete low-degree characterization | `thm:kbalgebra:low-degree` | `KBFold.ZKKernel.low_degree` |
| 04d-low-degree | corollary | Dimension of a kernel low-degree subspace | `cor:kbalgebra:dimension` | `KBFold.ZKKernel.dimension` |
| 04e-evaluation | definition | Multilinear equality weights | `def:kbalgebra:eq` | `KBFold.ZKKernel.eq` |
| 04e-evaluation | lemma | Kernel evaluation in factored form | `lem:kbalgebra:point-eval` | `KBFold.ZKKernel.point_eval` |
| 04e-evaluation | definition | Evaluation curve and scaling | `def:kbalgebra:curve` | `KBFold.ZKKernel.curve` |
| 04e-evaluation | lemma | One-factor scaled equality identity | `lem:kbalgebra:one-factor-eval` | `KBFold.ZKKernel.one_factor_eval` |
| 04e-evaluation | theorem | Scaled multilinear evaluation | `thm:kbalgebra:curve` | `KBFold.ZKKernel.curve` |
| 04e-evaluation | proposition | Exceptional-point bound | `prop:kbalgebra:exceptional` | `KBFold.ZKKernel.exceptional` |
| 04e-evaluation | corollary | Characteristic-two evaluation curve | `cor:kbalgebra:char2-curve` | `KBFold.ZKKernel.char2_curve` |
| 04f-fold-monomials | definition | Even--odd polynomial operators | `def:kbalgebra:evenodd` | `KBFold.ZKKernel.evenodd` |
| 04f-fold-monomials | lemma | Fold of a single monomial | `lem:kbalgebra:monomial-fold` | `KBFold.ZKKernel.monomial_fold` |
| 04f-fold-monomials | definition | Complete normalized fold | `def:kbalgebra:complete-fold` | `KBFold.ZKKernel.complete_fold` |
| 04f-fold-monomials | lemma | Degree halving | `lem:kbalgebra:halving` | `KBFold.ZKKernel.halving` |
| 04f-fold-monomials | lemma | Iterated fold of one monomial | `lem:kbalgebra:iterated-monomial` | `KBFold.ZKKernel.iterated_monomial` |
| 04f-fold-monomials | definition | Binary-exponent multilinearization | `def:kbalgebra:multilinearization` | `KBFold.ZKKernel.multilinearization` |
| 04f-fold-monomials | lemma | Multilinearization is a vector-space isomorphism | `lem:kbalgebra:multilinear-iso` | `KBFold.ZKKernel.multilinear_iso` |
| 04f-fold-monomials | lemma | Multilinearization of kernels, every characteristic | `lem:kbalgebra:multilinear-kernel` | `KBFold.ZKKernel.multilinear_kernel` |
| 04f-fold-monomials | definition | Tensor evaluation functional | `def:kbalgebra:weighted-eval` | `KBFold.ZKKernel.weighted_eval` |
| 04f-fold-monomials | theorem | Complete fold as a tensor functional | `thm:kbalgebra:tensor-fold` | `KBFold.ZKKernel.tensor_fold` |
| 04f-fold-monomials | corollary | Ordinary evaluation when all weights are invertible | `cor:kbalgebra:weighted-eval` | `KBFold.ZKKernel.weighted_eval` |
| 04f-fold-monomials | corollary | Characteristic-two fold identity | `cor:kbalgebra:char2-multilinear` | `KBFold.ZKKernel.char2_multilinear` |
| 04g-fri-masking | definition | Classical even--odd FRI fold | `def:kbalgebra:classical` | `KBFold.ZKKernel.classical` |
| 04g-fri-masking | lemma | Classical fold of the kernel coordinate pair | `lem:kbalgebra:classical-coordinates` | `KBFold.ZKKernel.classical_coordinates` |
| 04g-fri-masking | lemma | Classical versus normalized fold | `lem:kbalgebra:fold-reparam` | `KBFold.ZKKernel.fold_reparam` |
| 04g-fri-masking | lemma | One classical fold preserves evaluation on a square | `lem:kbalgebra:classical-eval` | `KBFold.ZKKernel.classical_eval` |
| 04g-fri-masking | theorem | Classical folding computes univariate evaluation | `thm:kbalgebra:classical-evaluation` | `KBFold.ZKKernel.classical_evaluation` |
| 04g-fri-masking | lemma | Naturality under field extensions | `lem:kbalgebra:naturality` | `KBFold.ZKKernel.naturality` |
| 04g-fri-masking | lemma | Degree of a high-degree masked kernel polynomial | `lem:kbalgebra:mask-degree` | `KBFold.ZKKernel.mask_degree` |
| 04g-fri-masking | corollary | The code dimension must change | `cor:kbalgebra:mask-rate` | `KBFold.ZKKernel.mask_rate` |
| 04h-mask-query | definition | Random low-degree kernel mask | `def:kbalgebra:random-mask` | `KBFold.ZKKernel.random_mask` |
| 04h-mask-query | lemma | Uniformity of the mask polynomial | `lem:kbalgebra:uniform-polynomial` | `KBFold.ZKKernel.uniform_polynomial` |
| 04h-mask-query | lemma | Uniform answers at prescribed nonzero points | `lem:kbalgebra:uniform-queries` | `KBFold.ZKKernel.uniform_queries` |
| 04h-mask-query | theorem | Adaptive bounded-query hiding for one masked polynomial | `thm:kbalgebra:adaptive-queries` | `KBFold.ZKKernel.adaptive_queries` |

| 04h-mask-query | theorem | Mask-query and code-rate tradeoff | `thm:kbalgebra:mask-rate-tradeoff` | `KBFold.ZKKernel.mask_rate_tradeoff` |

## Required dependency order

1. Finset / binary subset indexing and exponents.
2. Polynomial coefficient expansion and Kronecker basis.
3. Möbius inversion and low-degree block characterization.
4. Multilinear equality weights and evaluation curve.
5. Even/odd operators, weighted tensor fold and characteristic-two specialization.
6. Field base change, classical FRI comparison and degree-raising masks.
7. Finite-field randomness, interpolation, conditional affine spaces, adaptive query simulation.

## Existing Lean source correspondence

- Original KBFold: `lean/KBFold/Kernel.lean`, `LowDegree.lean`, `Mobius.lean`, and `WordFold.lean` (consult the repository for exact present paths).
- Do not duplicate existing certified code; transfer paper statements into the existing typed definitions and prove only compatibility lemmas.
- The paper-level algebra is independent of a concrete commitment; oracle-simulation statements require the Chapter 3 security model.

## Caveats

- Ordinary `M(P)(1+r)` equals the complete normalized fold **only in characteristic two**.
- In odd characteristic, use the weighted tensor functional `Lambda_r` or its carefully qualified reparametrized evaluation formula.
- Any finite uniform sampling claims require a **finite field**; the underlying basis and fold identities are valid for arbitrary fields.
- The bounded-query masking theorem concerns **one masked polynomial oracle** and is not the ZK theorem for KBFold.
- Codeword degree and rate change for nonzero `X^N R`; the existing final check cannot remain unchanged.
