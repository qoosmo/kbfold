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
