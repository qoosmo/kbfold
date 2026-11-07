# Chapter 7 — Binary-Field Packing and Transposition: Lean 4 Map

**Paper proof audit:** 71 labeled definitions/statements, including 22 definitions and **49 complete paper proofs** in seven sections. Proof counts match each non-definition statement. The new statements are not yet Lean-certified.

| Source | Kind | Exact title | LaTeX label | Suggested Lean 4 declaration | Status |
|---|---|---|---|---|---|
| `07a-packing.tex` | definition | Boolean witness and its field embedding | `def:pack:witness` | `ZKPacking.witness` | typed definition |
| `07a-packing.tex` | definition | Packing a Boolean column | `def:pack:pack` | `ZKPacking.pack` | typed definition |
| `07a-packing.tex` | lemma | Unpack after Pack | `lem:pack:unpack-pack` | `ZKPacking.unpack_pack` | complete paper proof |
| `07a-packing.tex` | lemma | Pack after Unpack | `lem:pack:pack-unpack` | `ZKPacking.pack_unpack` | complete paper proof |
| `07a-packing.tex` | lemma | Packing is binary-linear | `lem:pack:linear` | `ZKPacking.linear` | complete paper proof |
| `07a-packing.tex` | theorem | Lossless Boolean packing | `thm:pack:bijection` | `ZKPacking.bijection` | complete paper proof |
| `07a-packing.tex` | definition | Packed witness and its column coordinates | `def:pack:columns` | `ZKPacking.columns` | typed definition |
| `07a-packing.tex` | corollary | Recovering every Boolean witness bit | `cor:pack:column-bits` | `ZKPacking.column_bits` | complete paper proof |
| `07a-packing.tex` | definition | Multilinear evaluation weights | `def:pack:weights` | `ZKPacking.weights` | typed definition |
| `07a-packing.tex` | lemma | Two-axis equality-weight factorization | `lem:pack:weight-factor` | `ZKPacking.weight_factor` | complete paper proof |
| `07a-packing.tex` | corollary | Packed witness is the original Boolean multilinear table | `cor:pack:original-evaluation` | `ZKPacking.original_evaluation` | complete paper proof |
| `07a-packing.tex` | lemma | Partition of evaluation weights | `lem:pack:weight-sum` | `ZKPacking.weight_sum` | complete paper proof |
| `07b-transposition.tex` | definition | Binary coordinate matrix | `def:pack:matrix` | `ZKPacking.matrix` | typed definition |
| `07b-transposition.tex` | lemma | Recovering a field vector from its matrix | `lem:pack:matrix-reconstruct` | `ZKPacking.matrix_reconstruct` | complete paper proof |
| `07b-transposition.tex` | definition | Binary coordinate transpose | `def:pack:transpose` | `ZKPacking.transpose` | typed definition |
| `07b-transposition.tex` | lemma | Transpose is binary-linear | `lem:pack:transpose-linear` | `ZKPacking.transpose_linear` | complete paper proof |
| `07b-transposition.tex` | lemma | Coordinates of a transposed vector | `lem:pack:transpose-coords` | `ZKPacking.transpose_coords` | complete paper proof |
| `07b-transposition.tex` | theorem | Transposition is an involution | `thm:pack:transpose-involutive` | `ZKPacking.transpose_involutive` | complete paper proof |
| `07b-transposition.tex` | corollary | Transpose is a bijective binary-linear map | `cor:pack:transpose-iso` | `ZKPacking.transpose_iso` | complete paper proof |
| `07b-transposition.tex` | lemma | The coordinate matrices are transposes | `lem:pack:matrix-transpose` | `ZKPacking.matrix_transpose` | complete paper proof |
| `07b-transposition.tex` | lemma | Nonzero field elements have some nonzero coordinate | `lem:pack:coordinate-separates` | `ZKPacking.coordinate_separates` | complete paper proof |
| `07b-transposition.tex` | proposition | Transposition is not extension-field-linear | `prop:pack:not-L-linear` | `ZKPacking.not_L_linear` | complete paper proof |
| `07b-transposition.tex` | lemma | Uniformity under binary transposition | `lem:pack:transpose-uniform` | `ZKPacking.transpose_uniform` | complete paper proof |
| `07c-packed-evaluation.tex` | definition | Partial evaluations of the original Boolean witness | `def:pack:partials` | `ZKPacking.partials` | typed definition |
| `07c-packed-evaluation.tex` | lemma | Partial evaluations recover the claimed value | `lem:pack:partial-eval` | `ZKPacking.partial_eval` | complete paper proof |
| `07c-packed-evaluation.tex` | lemma | Coordinate of a Boolean partial sum | `lem:pack:partial-coordinate` | `ZKPacking.partial_coordinate` | complete paper proof |
| `07c-packed-evaluation.tex` | theorem | Packed transposition identity | `thm:pack:transpose-packed` | `ZKPacking.transpose_packed` | complete paper proof |
| `07c-packed-evaluation.tex` | definition | Random batching weights | `def:pack:batch` | `ZKPacking.batch` | typed definition |
| `07c-packed-evaluation.tex` | lemma | Linearity of batching over the binary prime field | `lem:pack:batch-add` | `ZKPacking.batch_add` | complete paper proof |
| `07c-packed-evaluation.tex` | theorem | Packed evaluation batching identity | `thm:pack:batch-correct` | `ZKPacking.batch_correct` | complete paper proof |
| `07c-packed-evaluation.tex` | definition | Transposition discrepancy polynomial | `def:pack:batch-error` | `ZKPacking.batch_error` | typed definition |
| `07c-packed-evaluation.tex` | lemma | Nonzero vector gives a nonzero discrepancy | `lem:pack:batch-nonzero` | `ZKPacking.batch_nonzero` | complete paper proof |
| `07c-packed-evaluation.tex` | theorem | Unmasked batching soundness | `thm:pack:batch-sound` | `ZKPacking.batch_sound` | complete paper proof |
| `07c-packed-evaluation.tex` | definition | Kernel representation of a transposed vector | `def:pack:kernel-transpose` | `ZKPacking.kernel_transpose` | typed definition |
| `07c-packed-evaluation.tex` | lemma | Kernel-fold representation of batching | `lem:pack:kernel-batch` | `ZKPacking.kernel_batch` | complete paper proof |
| `07d-masked-equations.tex` | definition | Field pads and masked partial evaluations | `def:pack:pads` | `ZKPacking.pads` | typed definition |
| `07d-masked-equations.tex` | lemma | Uniform masked partial evaluations | `lem:pack:masked-uniform` | `ZKPacking.masked_uniform` | complete paper proof |
| `07d-masked-equations.tex` | definition | Transposed pad coefficients | `def:pack:pad-coeff` | `ZKPacking.pad_coeff` | typed definition |
| `07d-masked-equations.tex` | lemma | Pad correction equals its complete kernel fold | `lem:pack:pad-kernel` | `ZKPacking.pad_kernel` | complete paper proof |
| `07d-masked-equations.tex` | lemma | Transpose of a masked vector | `lem:pack:masked-transpose` | `ZKPacking.masked_transpose` | complete paper proof |
| `07d-masked-equations.tex` | corollary | Masked batching with the true correction | `cor:pack:masked-batch` | `ZKPacking.masked_batch` | complete paper proof |
| `07d-masked-equations.tex` | definition | Candidate correction and outgoing interface | `def:pack:candidate-c` | `ZKPacking.candidate_c` | typed definition |
| `07d-masked-equations.tex` | lemma | Outgoing equation with consistent correction | `lem:pack:outgoing-honest` | `ZKPacking.outgoing_honest` | complete paper proof |
| `07d-masked-equations.tex` | definition | Incoming masked scalar | `def:pack:incoming` | `ZKPacking.incoming` | typed definition |
| `07d-masked-equations.tex` | lemma | Incoming masked scalar is uniform | `lem:pack:incoming-uniform` | `ZKPacking.incoming_uniform` | complete paper proof |
| `07d-masked-equations.tex` | lemma | Joint uniformity of basic public masks | `lem:pack:joint-uniform` | `ZKPacking.joint_uniform` | complete paper proof |
| `07d-masked-equations.tex` | definition | Incoming affine relation | `def:pack:incoming-check` | `ZKPacking.incoming_check` | typed definition |
| `07d-masked-equations.tex` | lemma | Incoming elimination of both masks | `lem:pack:incoming-eliminate` | `ZKPacking.incoming_eliminate` | complete paper proof |
| `07d-masked-equations.tex` | theorem | Perfect correctness of both masked interfaces | `thm:pack:honest-interfaces` | `ZKPacking.honest_interfaces` | complete paper proof |
| `07e-composition-soundness.tex` | definition | The three public-value constraints | `def:pack:interfaces` | `ZKPacking.interfaces` | typed definition |
| `07e-composition-soundness.tex` | definition | Partial-evaluation and correction errors | `def:pack:errors` | `ZKPacking.errors` | typed definition |
| `07e-composition-soundness.tex` | lemma | Exact outgoing discrepancy decomposition | `lem:pack:out-error` | `ZKPacking.out_error` | complete paper proof |
| `07e-composition-soundness.tex` | lemma | A correct correction isolates the partial-evaluation error | `lem:pack:out-isolates` | `ZKPacking.out_isolates` | complete paper proof |
| `07e-composition-soundness.tex` | lemma | A false claim and the incoming relations force a row error | `lem:pack:false-forces-error` | `ZKPacking.false_forces_error` | complete paper proof |
| `07e-composition-soundness.tex` | theorem | False-claim soundness with exact correction | `thm:pack:sound-exact` | `ZKPacking.sound_exact` | complete paper proof |
| `07e-composition-soundness.tex` | definition | Combined algebraic acceptance event | `def:pack:combined` | `ZKPacking.combined` | typed definition |
| `07e-composition-soundness.tex` | theorem | Complete algebraic soundness of packed Ring Switching | `thm:pack:algebraic-sound` | `ZKPacking.algebraic_sound` | complete paper proof |
| `07e-composition-soundness.tex` | theorem | Complete algebraic correctness of packed Ring Switching | `thm:pack:algebraic-complete` | `ZKPacking.algebraic_complete` | complete paper proof |
| `07f-affine-and-privacy.tex` | definition | Available affine constraints | `def:pack:affine-API` | `ZKPacking.affine_API` | typed definition |
| `07f-affine-and-privacy.tex` | lemma | Incoming constraints are extension-field affine | `lem:pack:IN-affine` | `ZKPacking.IN_affine` | complete paper proof |
| `07f-affine-and-privacy.tex` | lemma | Outgoing constraints are extension-field affine | `lem:pack:OUT-affine` | `ZKPacking.OUT_affine` | complete paper proof |
| `07f-affine-and-privacy.tex` | definition | Affine correction coefficients | `def:pack:affine-H` | `ZKPacking.affine_H` | typed definition |
| `07f-affine-and-privacy.tex` | lemma | Every correction expression is extension-field affine | `lem:pack:V-affine` | `ZKPacking.V_affine` | complete paper proof |
| `07f-affine-and-privacy.tex` | theorem | Trace-coordinate interface for candidate correction | `thm:pack:trace-correct` | `ZKPacking.trace_correct` | complete paper proof |
| `07f-affine-and-privacy.tex` | lemma | A revealed transposed pad reveals the original pad | `lem:pack:reveal-pad` | `ZKPacking.reveal_pad` | complete paper proof |
| `07f-affine-and-privacy.tex` | theorem | Revealing the correction destroys masking | `thm:pack:reveal-leak` | `ZKPacking.reveal_leak` | complete paper proof |
| `07f-affine-and-privacy.tex` | corollary | Masked-value uniformity alone does not imply privacy | `cor:pack:uniform-not-ZK` | `ZKPacking.uniform_not_ZK` | complete paper proof |
| `07g-proof-boundaries.tex` | definition | Ideal versus implemented acceptance | `def:pack:implementation` | `ZKPacking.implementation` | typed definition |
| `07g-proof-boundaries.tex` | lemma | Bad-execution decomposition | `lem:pack:bad-decomposition` | `ZKPacking.bad_decomposition` | complete paper proof |
| `07g-proof-boundaries.tex` | proposition | Conditional soundness under an external failure bound | `prop:pack:external-composition` | `ZKPacking.external_composition` | complete paper proof |
| `07g-proof-boundaries.tex` | definition | Formal verification obligations | `def:pack:obligations` | `ZKPacking.obligations` | typed definition |

## Lean modules in dependency order

1. `ZKPacking/Packing.lean`: index types, Boolean witness, pack/unpack, evaluation weight factorization.
2. `ZKPacking/Transpose.lean`: coordinate matrix, involution, $ℽ_2$-linearity and failure of $L$-linearity.
3. `ZKPacking/Evaluation.lean`: partial sums, packed transpose, affine batching, discrepancy root count.
4. `ZKPacking/MaskedInterfaces.lean`: uniform field pads, kernel correction, incoming/outgoing affine identities.
5. `ZKPacking/CompositionSoundness.lean`: exact residual decomposition, correct-claim completeness, two-challenge false-claim soundness.
6. `ZKPacking/AffineProofAPI.lean`: field-affine interfaces, trace verification, disclosure attack.
7. `ZKPacking/ProtocolBoundary.lean`: ideal-versus-implemented acceptance and conditional union-bound composition.

## Main exact identities

```text
Pack : (I → F₂) ≃ₗ[F₂] L
T : (I → L) ≃ₗ[F₂] (I → L)
T(T(s)) = s
coord_v(T(s)_u) = coord_u(s_v)
T(s*)_u = Σ_j coord_u(h_j) * packed_w_j
B_(s*)(theta) = Σ_j a_j(theta) * packed_w_j
m = s* + p
c^p = T(p)
Delta_p(theta) = PFold_theta(C_p)
CLAIM: y' = y_pub + p_in
IN: Σ_v q_v m_v + y' = Σ_v q_v p_v + p_in
OUT: Σ_j a_j(theta) packed_w_j = B_m(theta)+D_c(theta)
e = m+s*+p
kappa = c+c^p
OUT residual = B_e(theta)+D_kappa(theta)
Pr[false claim accepted] ≤ (ell+n)/2^n
```

The algebraic soundness bound presupposes: the Boolean witness, packed field elements, public masked values, hidden pads and candidate correction are fixed **before** the uniform first challenge $θ$; the Chapter 6 checker residuals are fixed before the independent uniform challenge $z$; and the public scalar $A$ may depend on $z$. This is the **ideal algebraic model**, not a complete PCS/IOP zero-knowledge or computational soundness theorem.

## Cryptographic and formalization gaps

- Bit/packed-witness consistency under the actual commitment scheme.
- Affine-proof/commitment soundness and knowledge extraction at the required time ordering.
- Joint simulation of public `m,y',U,A` plus commitment roots and authenticated openings.
- The characteristic-two extension is not the same folding code as the original odd-characteristic KBFold PCS.
- The entire transposed pad table `c^p` must remain hidden: revealing it alongside `m` recovers the unmasked partial vector `s*`.
- Any originality claim relative to Diamond--Posen, Kochergin, and Frigo--shelat requires a separate literature assessment.

## Reproducibility

The repository's Rust audit tests the packing/unpacking bijection, transposition involution, exact evaluation equations, hidden pad correction and residual decomposition over GF(16) and GF(256). It supplements but does not formally certify the proofs.
