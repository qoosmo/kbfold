# Chapter 5 — Lean 4 theorem map

**Scope:** Multilinear restrictions, arbitrary-characteristic normalized folds, the exact degree-aware masked polynomial chain, odd-characteristic codeword folding, local closure tests, and the joint fixed-schedule oracle masking criterion.

**Audit:** 64 labeled definitions/results; 51 mathematical results with complete proofs in LaTeX. These are **paper proofs**, not yet new Lean-certified results.

## Statement-by-statement map

| Source subsection | Kind | Exact statement title | LaTeX label | Proposed Lean declaration | Current status |
|---|---|---|---|---|---|
| `05a-prefix-restriction` | definition | Prefix equality weight | `def:kbff:prefix-weight` | `ZKFold.prefix_weight` | Typed definition |
| `05a-prefix-restriction` | lemma | First-bit factorization | `lem:kbff:weight-factor` | `ZKFold.weight_factor` | Paper proof |
| `05a-prefix-restriction` | definition | Simultaneous prefix restriction | `def:kbff:prefix-restriction` | `ZKFold.prefix_restriction` | Typed definition |
| `05a-prefix-restriction` | lemma | Zero-prefix identity | `lem:kbff:prefix-zero` | `ZKFold.prefix_zero` | Paper proof |
| `05a-prefix-restriction` | lemma | Prefix extension by one restriction | `lem:kbff:prefix-step` | `ZKFold.prefix_step` | Paper proof |
| `05a-prefix-restriction` | lemma | Linearity of prefix restriction | `lem:kbff:prefix-linear` | `ZKFold.prefix_linear` | Paper proof |
| `05a-prefix-restriction` | lemma | Partial multilinear-evaluation identity | `lem:kbff:prefix-mle` | `ZKFold.prefix_mle` | Paper proof |
| `05a-prefix-restriction` | corollary | Complete prefix restriction | `cor:kbff:full-prefix` | `ZKFold.full_prefix` | Paper proof |
| `05b-polynomial-fold` | definition | Bitwise fold weights | `def:kbff:bit-weights` | `ZKFold.bit_weights` | Typed definition |
| `05b-polynomial-fold` | lemma | Monomial fold, even exponent | `lem:kbff:fold-even` | `ZKFold.fold_even` | Paper proof |
| `05b-polynomial-fold` | lemma | Monomial fold, odd exponent | `lem:kbff:fold-odd` | `ZKFold.fold_odd` | Paper proof |
| `05b-polynomial-fold` | definition | Iterated normalized polynomial fold | `def:kbff:fold-iterate` | `ZKFold.fold_iterate` | Typed definition |
| `05b-polynomial-fold` | lemma | Iterated fold of a monomial | `lem:kbff:fold-monomial` | `ZKFold.fold_monomial` | Paper proof |
| `05b-polynomial-fold` | theorem | Explicit polynomial-fold formula | `thm:kbff:fold-coefficients` | `ZKFold.fold_coefficients` | Paper proof |
| `05b-polynomial-fold` | corollary | Degree-halving bound | `cor:kbff:fold-degree` | `ZKFold.fold_degree` | Paper proof |
| `05b-polynomial-fold` | corollary | Complete tensor functional | `cor:kbff:fold-tensor` | `ZKFold.fold_tensor` | Paper proof |
| `05b-polynomial-fold` | definition | Binary-exponent multilinearization | `def:kbff:ml` | `ZKFold.ml` | Typed definition |
| `05b-polynomial-fold` | lemma | Characteristic-two specialization | `lem:kbff:char2` | `ZKFold.char2` | Paper proof |
| `05b-polynomial-fold` | proposition | Failure of the unshifted characteristic-two identity in odd characteristic | `prop:kbff:not-char2` | `ZKFold.not_char2` | Paper proof |
| `05c-fold-dictionary` | lemma | First-bit kernel decomposition | `lem:kbff:kernel-first` | `ZKFold.kernel_first` | Paper proof |
| `05c-fold-dictionary` | lemma | Single-fold intertwining | `lem:kbff:intertwining` | `ZKFold.intertwining` | Paper proof |
| `05c-fold-dictionary` | theorem | Iterated folding--restriction dictionary | `thm:kbff:iterated-dictionary` | `ZKFold.iterated_dictionary` | Paper proof |
| `05c-fold-dictionary` | corollary | Complete fold equals multilinear evaluation | `cor:kbff:full-evaluation` | `ZKFold.full_evaluation` | Paper proof |
| `05c-fold-dictionary` | corollary | Two descriptions of the complete fold | `cor:kbff:two-functional` | `ZKFold.two_functional` | Paper proof |
| `05c-fold-dictionary` | lemma | Composition of prefix restrictions | `lem:kbff:restriction-compose` | `ZKFold.restriction_compose` | Paper proof |
| `05c-fold-dictionary` | corollary | Compatibility of nested polynomial folds | `cor:kbff:fold-compose` | `ZKFold.fold_compose` | Paper proof |
| `05d-masked-module` | definition | Mask degree and extended encoding | `def:kbff:mask-encoding` | `ZKFold.mask_encoding` | Typed definition |
| `05d-masked-module` | lemma | No overlap between table and high-degree masks | `lem:kbff:direct-sum` | `ZKFold.direct_sum` | Paper proof |
| `05d-masked-module` | proposition | Extended encoding is a linear isomorphism | `prop:kbff:extended-iso` | `ZKFold.extended_iso` | Paper proof |
| `05d-masked-module` | lemma | Fold of an even monomial shift | `lem:kbff:even-shift` | `ZKFold.even_shift` | Paper proof |
| `05d-masked-module` | definition | Masked-table and residual-mask sequences | `def:kbff:masked-chain` | `ZKFold.masked_chain` | Typed definition |
| `05d-masked-module` | theorem | Masked folding invariant at every level | `thm:kbff:masked-invariant` | `ZKFold.masked_invariant` | Paper proof |
| `05d-masked-module` | lemma | Degree of the residual mask | `lem:kbff:residual-degree` | `ZKFold.residual_degree` | Paper proof |
| `05d-masked-module` | corollary | Exact upper degree budget | `cor:kbff:masked-degree` | `ZKFold.masked_degree` | Paper proof |
| `05d-masked-module` | lemma | Residual mask is constant at the final level | `lem:kbff:residual-constant` | `ZKFold.residual_constant` | Paper proof |
| `05d-masked-module` | theorem | Linear final closure for high-degree masked KBFold | `thm:kbff:linear-closure` | `ZKFold.linear_closure` | Paper proof |
| `05d-masked-module` | corollary | Constant-term closure identity | `cor:kbff:masked-constant` | `ZKFold.masked_constant` | Paper proof |
| `05e-codeword-fold` | lemma | Domain sizes | `lem:kbff:domain-sizes` | `ZKFold.domain_sizes` | Paper proof |
| `05e-codeword-fold` | definition | Word fold on a smooth domain | `def:kbff:wordfold` | `ZKFold.wordfold` | Typed definition |
| `05e-codeword-fold` | lemma | Word fold is well defined | `lem:kbff:wordfold-well-defined` | `ZKFold.wordfold_well_defined` | Paper proof |
| `05e-codeword-fold` | lemma | Evaluations split into even and odd parts | `lem:kbff:eval-evenodd` | `ZKFold.eval_evenodd` | Paper proof |
| `05e-codeword-fold` | theorem | Word/polynomial fold commutation | `thm:kbff:wordfold` | `ZKFold.wordfold` | Paper proof |
| `05e-codeword-fold` | corollary | Masked oracle fold chain | `cor:kbff:wordchain` | `ZKFold.wordchain` | Paper proof |
| `05e-codeword-fold` | definition | Enlarged degree budgets | `def:kbff:degree-budgets` | `ZKFold.degree_budgets` | Typed definition |
| `05e-codeword-fold` | lemma | Budget recurrence | `lem:kbff:budget-recurrence` | `ZKFold.budget_recurrence` | Paper proof |
| `05e-codeword-fold` | theorem | Degree-correct masked RS chain | `thm:kbff:code-rate` | `ZKFold.code_rate` | Paper proof |
| `05e-codeword-fold` | corollary | Exact rate transition for a power-of-two mask budget | `cor:kbff:rate-transition` | `ZKFold.rate_transition` | Paper proof |
| `05f-local-verification` | definition | Fold-consistency residual | `def:kbff:fold-residual` | `ZKFold.fold_residual` | Typed definition |
| `05f-local-verification` | lemma | Local test equals a residual root | `lem:kbff:local-residual` | `ZKFold.local_residual` | Paper proof |
| `05f-local-verification` | lemma | Residual degree | `lem:kbff:residual-bound` | `ZKFold.residual_bound` | Paper proof |
| `05f-local-verification` | theorem | Single-query local fold detection | `thm:kbff:local-detection` | `ZKFold.local_detection` | Paper proof |
| `05f-local-verification` | definition | Linear final closure predicate | `def:kbff:linear-predicate` | `ZKFold.linear_predicate` | Typed definition |
| `05f-local-verification` | lemma | Honest masked closure | `lem:kbff:honest-closure` | `ZKFold.honest_closure` | Paper proof |
| `05f-local-verification` | lemma | Two evaluations determine the constant of a line | `lem:kbff:two-point-line` | `ZKFold.two_point_line` | Paper proof |
| `05f-local-verification` | corollary | Two-point linear closure check | `cor:kbff:two-point-close` | `ZKFold.two_point_close` | Paper proof |
| `05g-joint-observations` | definition | Fixed fold-query schedule | `def:kbff:schedule` | `ZKFold.schedule` | Typed definition |
| `05g-joint-observations` | definition | Witness and mask observation maps | `def:kbff:observation-maps` | `ZKFold.observation_maps` | Typed definition |
| `05g-joint-observations` | lemma | Both observation maps are linear | `lem:kbff:observation-linear` | `ZKFold.observation_linear` | Paper proof |
| `05g-joint-observations` | lemma | Exact observation decomposition | `lem:kbff:observation-decompose` | `ZKFold.observation_decompose` | Paper proof |
| `05g-joint-observations` | theorem | Exact joint fixed-schedule masking criterion | `thm:kbff:joint-mask` | `ZKFold.joint_mask` | Paper proof |
| `05g-joint-observations` | corollary | Sufficient condition for witness-independent fixed-schedule answers | `cor:kbff:joint-surjective` | `ZKFold.joint_surjective` | Paper proof |
| `05g-joint-observations` | lemma | Dimension obstruction to surjectivity | `lem:kbff:rank-obstruction` | `ZKFold.rank_obstruction` | Paper proof |
| `05g-joint-observations` | theorem | One-query attack on a reused degree-zero mask | `thm:kbff:one-query-attack` | `ZKFold.one_query_attack` | Paper proof |
| `05g-joint-observations` | corollary | Separate uniform marginals are insufficient | `cor:kbff:uniform-marginals` | `ZKFold.uniform_marginals` | Paper proof |

## Dependency-order Lean modules

1. `ZKFold/PrefixRestriction.lean` — equality weights, prefix restriction, multilinear evaluations; field only.
2. `ZKFold/PolynomialFold.lean` — global normalized fold, monomial weights, iteration, characteristic-two specialization.
3. `ZKFold/FoldDictionary.lean` — kernel encoding commutes with restriction, iterated dictionary, prefix composition.
4. `ZKFold/MaskedModule.lean` — direct-sum embedding, high-degree masks, degree budget, linear final closure.
5. `ZKFold/CodewordFold.lean` — odd characteristic, multiplicative 2-power subgroup, word fold, RS rate bounds.
6. `ZKFold/LocalVerification.lean` — root-count detection under degree membership and two-point linear closure.
7. `ZKFold/JointMasking.lean` — finite-field linear mask image, uniform cosets, exact total-variation criterion for fixed schedules and an explicit one-query joint-leakage attack.

## Algebraic interface to subsequent ZK-KBFold chapters

Let `N=2^m`, `1 ≤ B ≤ N`, `deg R<B`, and `Q₀=U_f + X^N R`. Theorems from this chapter establish:
- `Qⱼ=U_(Res^[j] f) + X^(N/2^j) PFold^[j](R)`;
- `deg Qⱼ < N/2^j + ceil(B/2^j)`;
- `Q_m = MLE(f)(r) + rho_r(R)*X`, hence `coeff(Q_m,0)=MLE(f)(r)`;
- local word-fold verification against degree-bounded polynomials;
- exact fixed-schedule joint privacy criterion `S(f-g) ∈ range(T)`;
- **reused-mask attack:** even when an initial opening and the final line slope are each uniform, their joint distribution can reveal the witness perfectly.

**Unproved protocol obligations:** malicious non-codeword soundness at the increased code rate, masked Sumcheck, authenticated-oracle online simulator, and QROM compilation. None follows merely from the algebraic theorems.

**Source attribution:** The unmasked kernel dictionary is from the original KBFold paper. The structural high-degree masking proposal is noted there as future work. This chapter supplies an explicit linear closure invariant and a precise joint mask-image test; originality beyond the cited literature must be assessed separately.
