# Chapter 6 — Characteristic-Two Specializations: Lean 4 Theorem Map

**Audit:** 85 individually labeled definitions/results, including 18 definitions and **67 full paper proofs**. All eight source subsections have matching proof environments for every non-definition statement. **No new declaration in this chapter is claimed to be machine-checked.**

## Statement-by-statement plan

| Source | Kind | Statement | LaTeX label | Proposed Lean declaration | Status |
|---|---|---|---|---|---|
| `06a-frobenius` | lemma | Characteristic-two squaring | `lem:binary:square` | `ZKBinary.square` | Paper proof |
| `06a-frobenius` | lemma | Iterated Frobenius additivity | `lem:binary:frob-add` | `ZKBinary.frob_add` | Paper proof |
| `06a-frobenius` | definition | Frobenius on scalars | `def:binary:frob-scalar` | `ZKBinary.frob_scalar` | Definition |
| `06a-frobenius` | lemma | Frobenius endomorphism | `lem:binary:frob-ring` | `ZKBinary.frob_ring` | Paper proof |
| `06a-frobenius` | lemma | Frobenius is injective | `lem:binary:frob-injective` | `ZKBinary.frob_injective` | Paper proof |
| `06a-frobenius` | corollary | Frobenius permutes a finite field | `cor:binary:frob-bijective` | `ZKBinary.frob_bijective` | Paper proof |
| `06a-frobenius` | definition | Coefficient Frobenius of a polynomial | `def:binary:poly-frob` | `ZKBinary.poly_frob` | Definition |
| `06a-frobenius` | lemma | Polynomial Frobenius identity | `lem:binary:poly-frob` | `ZKBinary.poly_frob` | Paper proof |
| `06a-frobenius` | lemma | Coefficient Frobenius and products | `lem:binary:poly-frob-mult` | `ZKBinary.poly_frob_mult` | Paper proof |
| `06b-kernel-frobenius` | lemma | Binary coefficients of a kernel | `lem:binary:binary-coeffs` | `ZKBinary.binary_coeffs` | Paper proof |
| `06b-kernel-frobenius` | lemma | Kernel coefficient Frobenius invariance | `lem:binary:kernel-coeff-frob` | `ZKBinary.kernel_coeff_frob` | Paper proof |
| `06b-kernel-frobenius` | theorem | Kernel Frobenius substitution | `thm:binary:kernel-square` | `ZKBinary.kernel_square` | Paper proof |
| `06b-kernel-frobenius` | definition | Kernel coefficient Frobenius | `def:binary:table-frob` | `ZKBinary.table_frob` | Definition |
| `06b-kernel-frobenius` | theorem | Frobenius covariance of kernel encoding | `thm:binary:encoding-frob` | `ZKBinary.encoding_frob` | Paper proof |
| `06b-kernel-frobenius` | lemma | Kernel partition sum | `lem:binary:partition` | `ZKBinary.partition` | Paper proof |
| `06b-kernel-frobenius` | corollary | All-one kernel coordinates of the constant polynomial | `cor:binary:one-coeffs` | `ZKBinary.one_coeffs` | Paper proof |
| `06b-kernel-frobenius` | lemma | Two complementary lowest-bit kernels | `lem:binary:complementary` | `ZKBinary.complementary` | Paper proof |
| `06c-multilinearization` | definition | Binary-exponent multilinearization | `def:binary:ml` | `ZKBinary.ml` | Definition |
| `06c-multilinearization` | lemma | Multilinearization is a vector-space isomorphism | `lem:binary:ml-iso` | `ZKBinary.ml_iso` | Paper proof |
| `06c-multilinearization` | lemma | Explicit subset expansion of a kernel | `lem:binary:kernel-expansion` | `ZKBinary.kernel_expansion` | Paper proof |
| `06c-multilinearization` | lemma | Multilinearization of every kernel basis element | `lem:binary:ml-kernel` | `ZKBinary.ml_kernel` | Paper proof |
| `06c-multilinearization` | definition | Characteristic-two equality weights | `def:binary:lambda` | `ZKBinary.lambda` | Definition |
| `06c-multilinearization` | lemma | Equality weights agree | `lem:binary:eq-weights` | `ZKBinary.eq_weights` | Paper proof |
| `06c-multilinearization` | lemma | Boolean weights partition unity | `lem:binary:lambda-partition` | `ZKBinary.lambda_partition` | Paper proof |
| `06c-multilinearization` | theorem | Complete kernel fold equals multilinearized evaluation | `thm:binary:fold-ml` | `ZKBinary.fold_ml` | Paper proof |
| `06c-multilinearization` | definition | Partial multilinearization | `def:binary:partial-ml` | `ZKBinary.partial_ml` | Definition |
| `06c-multilinearization` | lemma | Partial folding formula | `lem:binary:partial-fold` | `ZKBinary.partial_fold` | Paper proof |
| `06c-multilinearization` | lemma | Frobenius covariance of equality weights | `lem:binary:lambda-frob` | `ZKBinary.lambda_frob` | Paper proof |
| `06c-multilinearization` | corollary | Frobenius covariance of kernel-fold values | `cor:binary:fold-frob` | `ZKBinary.fold_frob` | Paper proof |
| `06d-trace-artin-schreier` | lemma | Frobenius has period $n$ | `lem:binary:frob-period` | `ZKBinary.frob_period` | Paper proof |
| `06d-trace-artin-schreier` | definition | Absolute trace | `def:binary:trace` | `ZKBinary.trace` | Definition |
| `06d-trace-artin-schreier` | lemma | Trace is additive and Frobenius-invariant | `lem:binary:trace-add` | `ZKBinary.trace_add` | Paper proof |
| `06d-trace-artin-schreier` | lemma | Trace takes binary values | `lem:binary:trace-binary` | `ZKBinary.trace_binary` | Paper proof |
| `06d-trace-artin-schreier` | lemma | Trace is surjective | `lem:binary:trace-surj` | `ZKBinary.trace_surj` | Paper proof |
| `06d-trace-artin-schreier` | corollary | Sizes of the two trace fibers | `cor:binary:trace-fibers` | `ZKBinary.trace_fibers` | Paper proof |
| `06d-trace-artin-schreier` | definition | Artin--Schreier operator | `def:binary:artin-schreier` | `ZKBinary.artin_schreier` | Definition |
| `06d-trace-artin-schreier` | lemma | Artin--Schreier is binary-linear | `lem:binary:as-linear` | `ZKBinary.as_linear` | Paper proof |
| `06d-trace-artin-schreier` | lemma | Artin--Schreier kernel | `lem:binary:as-kernel` | `ZKBinary.as_kernel` | Paper proof |
| `06d-trace-artin-schreier` | lemma | Every Artin--Schreier value has trace zero | `lem:binary:as-trace` | `ZKBinary.as_trace` | Paper proof |
| `06d-trace-artin-schreier` | theorem | Artin--Schreier characterizes trace zero | `thm:binary:as-image` | `ZKBinary.as_image` | Paper proof |
| `06d-trace-artin-schreier` | corollary | Uniform trace-zero masking | `cor:binary:as-uniform` | `ZKBinary.as_uniform` | Paper proof |
| `06d-trace-artin-schreier` | theorem | Perfect hiding of an individual trace-zero shift | `thm:binary:single-mask` | `ZKBinary.single_mask` | Paper proof |
| `06e-dual-coordinates` | lemma | Existence of an element of full binary degree | `lem:binary:full-degree-element` | `ZKBinary.full_degree_element` | Paper proof |
| `06e-dual-coordinates` | definition | Evaluation basis | `def:binary:eval-basis` | `ZKBinary.eval_basis` | Definition |
| `06e-dual-coordinates` | lemma | Kernel values form a binary field basis | `lem:binary:eval-basis` | `ZKBinary.eval_basis` | Paper proof |
| `06e-dual-coordinates` | definition | Binary coordinate maps | `def:binary:coords` | `ZKBinary.coords` | Definition |
| `06e-dual-coordinates` | lemma | Coordinate extraction | `lem:binary:extract` | `ZKBinary.extract` | Paper proof |
| `06e-dual-coordinates` | lemma | Trace pairing is nondegenerate | `lem:binary:trace-pairing` | `ZKBinary.trace_pairing` | Paper proof |
| `06e-dual-coordinates` | theorem | Existence and uniqueness of trace-dual coordinates | `thm:binary:dual-basis` | `ZKBinary.dual_basis` | Paper proof |
| `06e-dual-coordinates` | definition | Binary transpose and kernel correction | `def:binary:transpose` | `ZKBinary.transpose` | Definition |
| `06e-dual-coordinates` | lemma | Trace expression for the correction | `lem:binary:delta-trace` | `ZKBinary.delta_trace` | Paper proof |
| `06e-dual-coordinates` | definition | Public affine coefficients | `def:binary:affine-H` | `ZKBinary.affine_H` | Definition |
| `06e-dual-coordinates` | lemma | Affine transpose trace identity | `lem:binary:affine-trace` | `ZKBinary.affine_trace` | Paper proof |
| `06e-dual-coordinates` | lemma | Trace coordinates of affine residuals | `lem:binary:V-trace` | `ZKBinary.V_trace` | Paper proof |
| `06e-dual-coordinates` | theorem | Exact affine trace consistency | `thm:binary:affine-consistency` | `ZKBinary.affine_consistency` | Paper proof |
| `06e-dual-coordinates` | lemma | Mismatch gives a nonzero multilinear polynomial | `lem:binary:nonzero-mismatch` | `ZKBinary.nonzero_mismatch` | Paper proof |
| `06e-dual-coordinates` | corollary | Random-challenge detection of a coefficient mismatch | `cor:binary:mismatch-bound` | `ZKBinary.mismatch_bound` | Paper proof |
| `06f-masked-traces` | definition | Artin--Schreier-masked public values | `def:binary:masked-values` | `ZKBinary.masked_values` | Definition |
| `06f-masked-traces` | lemma | Masking preserves the trace of each residual | `lem:binary:mask-trace` | `ZKBinary.mask_trace` | Paper proof |
| `06f-masked-traces` | corollary | Consistency iff all public traces vanish | `cor:binary:masked-traces-consistent` | `ZKBinary.masked_traces_consistent` | Paper proof |
| `06f-masked-traces` | theorem | Joint uniformity of independently masked traces | `thm:binary:masked-vector-uniform` | `ZKBinary.masked_vector_uniform` | Paper proof |
| `06f-masked-traces` | definition | Algebraic consistency residual | `def:binary:residual` | `ZKBinary.residual` | Definition |
| `06f-masked-traces` | lemma | Trace of an algebraic residual | `lem:binary:residual-trace` | `ZKBinary.residual_trace` | Paper proof |
| `06f-masked-traces` | lemma | Trace checks force a nonzero residual under mismatch | `lem:binary:forced-residual` | `ZKBinary.forced_residual` | Paper proof |
| `06g-anchored-kernels` | lemma | Unanchored residual dependence | `lem:binary:unanchored` | `ZKBinary.unanchored` | Paper proof |
| `06g-anchored-kernels` | definition | Anchored Boolean kernels | `def:binary:anchored` | `ZKBinary.anchored` | Definition |
| `06g-anchored-kernels` | lemma | Anchored family degree | `lem:binary:anchor-degree` | `ZKBinary.anchor_degree` | Paper proof |
| `06g-anchored-kernels` | lemma | Sum of anchored kernels | `lem:binary:anchor-sum` | `ZKBinary.anchor_sum` | Paper proof |
| `06g-anchored-kernels` | theorem | Independence of the constant and all anchored kernels | `thm:binary:anchor-independence` | `ZKBinary.anchor_independence` | Paper proof |
| `06g-anchored-kernels` | corollary | Anchored family is a basis in degree at most $n$ | `cor:binary:anchor-basis` | `ZKBinary.anchor_basis` | Paper proof |
| `06g-anchored-kernels` | proposition | Degree-$n$ anchoring is dimensionally minimal | `prop:binary:anchor-minimal` | `ZKBinary.anchor_minimal` | Paper proof |
| `06g-anchored-kernels` | lemma | Anchored kernels commute with Frobenius evaluation | `lem:binary:anchor-frob` | `ZKBinary.anchor_frob` | Paper proof |
| `06g-anchored-kernels` | definition | Anchored residual polynomial | `def:binary:anchor-residual` | `ZKBinary.anchor_residual` | Definition |
| `06g-anchored-kernels` | lemma | Nonzero residual gives a nonzero polynomial | `lem:binary:anchor-nonzero` | `ZKBinary.anchor_nonzero` | Paper proof |
| `06g-anchored-kernels` | theorem | Root bound for an anchored residual | `thm:binary:anchor-root` | `ZKBinary.anchor_root` | Paper proof |
| `06h-consistency-check` | definition | Affine consistency checks | `def:binary:checks` | `ZKBinary.checks` | Definition |
| `06h-consistency-check` | definition | Scalar and vector checking residuals | `def:binary:check-residuals` | `ZKBinary.check_residuals` | Definition |
| `06h-consistency-check` | lemma | First equation determines the public scalar | `lem:binary:first-determines` | `ZKBinary.first_determines` | Paper proof |
| `06h-consistency-check` | lemma | The two affine checks imply an anchored residual root | `lem:binary:check-implies-root` | `ZKBinary.check_implies_root` | Paper proof |
| `06h-consistency-check` | lemma | Honest trace check | `lem:binary:honest-traces` | `ZKBinary.honest_traces` | Paper proof |
| `06h-consistency-check` | lemma | Honest affine checks | `lem:binary:honest-affine` | `ZKBinary.honest_affine` | Paper proof |
| `06h-consistency-check` | theorem | Perfect algebraic completeness | `thm:binary:checker-complete` | `ZKBinary.checker_complete` | Paper proof |
| `06h-consistency-check` | theorem | Conditional anchored-check soundness | `thm:binary:checker-conditional` | `ZKBinary.checker_conditional` | Paper proof |
| `06h-consistency-check` | theorem | Two-challenge coefficient-consistency bound | `thm:binary:two-challenge` | `ZKBinary.two_challenge` | Paper proof |
| `06h-consistency-check` | lemma | No even-order multiplicative subgroup in a binary field | `lem:binary:no-even-subgroup` | `ZKBinary.no_even_subgroup` | Paper proof |

## Certification modules in dependency order

1. `ZKBinary/Frobenius.lean`: field Frobenius, coefficient Frobenius, finite-field permutation.
2. `ZKBinary/KernelFrobenius.lean`: binary coefficient kernels, partition of unity, kernel covariance.
3. `ZKBinary/Multilinearization.lean`: explicit subset expansion, multilinearization, partial and complete folds.
4. `ZKBinary/AbsoluteTrace.lean`: trace as a binary linear functional, surjectivity, Artin--Schreier image and uniformity.
5. `ZKBinary/TraceCoordinates.lean`: full-degree element, evaluation basis, trace-dual basis and affine kernel correction.
6. `ZKBinary/MaskedTraces.lean`: conditional uniformity of trace-zero public values and forced residual.
7. `ZKBinary/AnchoredKernel.lean`: anchored basis, minimal degree, Frobenius root test.
8. `ZKBinary/ConsistencyChecker.lean`: exact algebraic checker, perfect completeness, two-challenge timing and soundness.

## Principal typed hypotheses

- `L` is a finite field of characteristic two and cardinality `2^n`.
- `n=2^ell`, `ell ≥ 1`, and the kernel index type has cardinality `n`.
- `alpha ∈ L` has extension degree `n`, and `beta_u=K_u(alpha)` is an `F₂`-basis.
- The trace-dual family `eta_u` satisfies `Tr(eta_u*beta_v)=δ_uv`.
- The candidate coefficients `c` and pads `p` are fixed before `theta`; public masks and affine values are fixed before the independent `z` challenge.
- The total degree bound on the mismatch polynomial is `ell`; anchored residual degree is at most `n`.

## Established algebraic identities

```text
K_b(X)^(2^j) = K_b(X^(2^j))
U_c(X)^(2^j) = U_(c^(2^j))(X^(2^j))
sum_b K_b(X) = 1                     [characteristic two only]
PFold_all(theta,P) = M(P)(1+theta)
Delta_p(theta) = PFold_all(theta,C_p)
Tr(V_k) = coord_k(D_c(theta)+Delta_p(theta))
im (t ↦ t²+t) = ker Tr
{1} ∪ {W_b} is a basis of L[X]_(≤n)
Pr[F_(delta,e)(z²)=0 | (delta,e)≠0] ≤ n/2^n
Pr[checker accepts | c≠c^p] ≤ (ell+n)/2^n
```

## Excluded protocol claims

The chapter's conditional mask-uniformity statement concerns the vector of trace-zero messages `U`, not their joint distribution with the later public scalar `A`. The algebraic two-challenge theorem does not prove: commitment binding, the entire Ring Switching reduction, an online ZK simulator, or odd-characteristic KBFold zero knowledge. The original odd-characteristic `±x` word-fold cannot be reused over binary fields.

**Historical attribution:** The binary ring-switching and Frobenius/trace-zero masking mechanisms are related to Diamond--Posen, Kochergin, and Frigo--shelat. New mathematical comparisons must be evaluated against those primary sources before any novelty claim.
