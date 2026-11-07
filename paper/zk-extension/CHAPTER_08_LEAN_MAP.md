# Chapter 8 — Diamond–Posen Ring Switching: Lean 4 Formalization Map

**Proof audit:** 56 individually labeled definitions/results, **41 complete paper proofs** in seven subsections. All stated non-definition results have an explicit proof block. **No new Chapter 8 Lean declaration is machine-certified yet.**

## Statement-by-statement dependency map

| Subsection | Kind | Theorem/definition | LaTeX label | Proposed Lean 4 declaration | Current status |
|---|---|---|---|---|---|
| `08a-tensor-algebra.tex` | definition | Two embeddings | `def:dpr:embeddings` | `ZKDPR.embeddings` | typed definition |
| `08a-tensor-algebra.tex` | lemma | The multiplication map is well defined | `lem:dpr:mu-defined` | `ZKDPR.mu_defined` | complete paper proof |
| `08a-tensor-algebra.tex` | lemma | Two commuting field embeddings | `lem:dpr:phi-embed` | `ZKDPR.phi_embed` | complete paper proof |
| `08a-tensor-algebra.tex` | definition | Column coordinates in the tensor algebra | `def:dpr:column` | `ZKDPR.column` | typed definition |
| `08a-tensor-algebra.tex` | lemma | Existence and uniqueness of tensor columns | `lem:dpr:column-basis` | `ZKDPR.column_basis` | complete paper proof |
| `08a-tensor-algebra.tex` | lemma | Columns of the two embeddings | `lem:dpr:embedding-columns` | `ZKDPR.embedding_columns` | complete paper proof |
| `08a-tensor-algebra.tex` | lemma | Left scalar multiplication acts columnwise | `lem:dpr:column-scaling` | `ZKDPR.column_scaling` | complete paper proof |
| `08a-tensor-algebra.tex` | definition | Weighted column contraction | `def:dpr:contraction` | `ZKDPR.contraction` | typed definition |
| `08a-tensor-algebra.tex` | lemma | Contraction is linear in the left scalar action | `lem:dpr:contraction-linear` | `ZKDPR.contraction_linear` | complete paper proof |
| `08a-tensor-algebra.tex` | lemma | Ordinary multiplication loses tensor information | `lem:dpr:multiplication-loss` | `ZKDPR.multiplication_loss` | complete paper proof |
| `08b-tensor-evaluation.tex` | definition | Packed multilinear polynomial | `def:dpr:packed-poly` | `ZKDPR.packed_poly` | typed definition |
| `08b-tensor-evaluation.tex` | lemma | Tensor expansion on Boolean columns | `lem:dpr:tensor-column` | `ZKDPR.tensor_column` | complete paper proof |
| `08b-tensor-evaluation.tex` | definition | Tensor partial evaluation | `def:dpr:tensor-S` | `ZKDPR.tensor_S` | typed definition |
| `08b-tensor-evaluation.tex` | lemma | Evaluation of equality weights through the left embedding | `lem:dpr:eq-embedded` | `ZKDPR.eq_embedded` | complete paper proof |
| `08b-tensor-evaluation.tex` | theorem | Columns of the tensor evaluation | `thm:dpr:column-evaluation` | `ZKDPR.column_evaluation` | complete paper proof |
| `08b-tensor-evaluation.tex` | theorem | Original evaluation is a column contraction | `thm:dpr:claim-contraction` | `ZKDPR.claim_contraction` | complete paper proof |
| `08b-tensor-evaluation.tex` | lemma | Multiplication recovers only the packed high-axis evaluation | `lem:dpr:mu-evaluation` | `ZKDPR.mu_evaluation` | complete paper proof |
| `08b-tensor-evaluation.tex` | definition | Sumcheck summand over $A$ | `def:dpr:H` | `ZKDPR.H` | typed definition |
| `08b-tensor-evaluation.tex` | lemma | Individual variable degree of the sumcheck summand | `lem:dpr:H-degree` | `ZKDPR.H_degree` | complete paper proof |
| `08b-tensor-evaluation.tex` | theorem | Tensor Boolean sum equals its partial evaluation | `thm:dpr:boolean-sum` | `ZKDPR.boolean_sum` | complete paper proof |
| `08b-tensor-evaluation.tex` | lemma | Reduction to a large-field evaluation at a common challenge | `lem:dpr:terminal` | `ZKDPR.terminal` | complete paper proof |
| `08c-sumcheck-over-tensor.tex` | lemma | Factor theorem for a commutative ring | `lem:dpr:factor` | `ZKDPR.factor` | complete paper proof |
| `08c-sumcheck-over-tensor.tex` | lemma | Units from the embedded challenge field | `lem:dpr:units` | `ZKDPR.units` | complete paper proof |
| `08c-sumcheck-over-tensor.tex` | theorem | Root bound inside the embedded field | `thm:dpr:ring-roots` | `ZKDPR.ring_roots` | complete paper proof |
| `08c-sumcheck-over-tensor.tex` | corollary | Uniform challenge root probability | `cor:dpr:ring-prob` | `ZKDPR.ring_prob` | complete paper proof |
| `08c-sumcheck-over-tensor.tex` | definition | True partial-sum polynomial | `def:dpr:true-partial` | `ZKDPR.true_partial` | typed definition |
| `08c-sumcheck-over-tensor.tex` | lemma | True sumcheck degree and endpoint identity | `lem:dpr:true-partial` | `ZKDPR.true_partial` | complete paper proof |
| `08c-sumcheck-over-tensor.tex` | definition | Degree-two tensor sumcheck | `def:dpr:sumcheck` | `ZKDPR.sumcheck` | typed definition |
| `08c-sumcheck-over-tensor.tex` | lemma | A false running claim forces a nonzero discrepancy | `lem:dpr:false-prefix` | `ZKDPR.false_prefix` | complete paper proof |
| `08c-sumcheck-over-tensor.tex` | lemma | One-round false-to-true transition bound | `lem:dpr:transition` | `ZKDPR.transition` | complete paper proof |
| `08c-sumcheck-over-tensor.tex` | theorem | Tensor sumcheck soundness | `thm:dpr:sumcheck-sound` | `ZKDPR.sumcheck_sound` | complete paper proof |
| `08d-protocol.tex` | definition | Underlying large-field evaluation interface | `def:dpr:large-pcs` | `ZKDPR.large_pcs` | typed definition |
| `08d-protocol.tex` | definition | Ring-switching prover and verifier | `def:dpr:full-protocol` | `ZKDPR.full_protocol` | typed definition |
| `08d-protocol.tex` | lemma | All verifier quantities are typed | `lem:dpr:welltyped` | `ZKDPR.welltyped` | complete paper proof |
| `08d-protocol.tex` | lemma | The public terminal equality factor is computable | `lem:dpr:terminal-public` | `ZKDPR.terminal_public` | complete paper proof |
| `08d-protocol.tex` | definition | Committed-word timing invariant | `def:dpr:timing` | `ZKDPR.timing` | typed definition |
| `08e-security-proofs.tex` | lemma | Honest initial contraction | `lem:dpr:init-honest` | `ZKDPR.init_honest` | complete paper proof |
| `08e-security-proofs.tex` | lemma | Honest sumcheck telescoping | `lem:dpr:telescoping` | `ZKDPR.telescoping` | complete paper proof |
| `08e-security-proofs.tex` | lemma | Honest terminal check | `lem:dpr:terminal-honest` | `ZKDPR.terminal_honest` | complete paper proof |
| `08e-security-proofs.tex` | theorem | Perfect completeness of the unmasked compiler | `thm:dpr:complete` | `ZKDPR.complete` | complete paper proof |
| `08e-security-proofs.tex` | definition | Unpacking an arbitrary committed polynomial | `def:dpr:extract` | `ZKDPR.extract` | typed definition |
| `08e-security-proofs.tex` | lemma | Packing after extraction gives the original packed polynomial | `lem:dpr:extract-pack` | `ZKDPR.extract_pack` | complete paper proof |
| `08e-security-proofs.tex` | lemma | False original claim implies false tensor initial sum | `lem:dpr:false-initial` | `ZKDPR.false_initial` | complete paper proof |
| `08e-security-proofs.tex` | lemma | A correct delegated opening implies the true terminal tensor value | `lem:dpr:correct-open` | `ZKDPR.correct_open` | complete paper proof |
| `08e-security-proofs.tex` | theorem | False-claim soundness with a bound underlying large-field oracle | `thm:dpr:compose-sound` | `ZKDPR.compose_sound` | complete paper proof |
| `08e-security-proofs.tex` | corollary | Ideal large-field oracle error | `cor:dpr:ideal-sound` | `ZKDPR.ideal_sound` | complete paper proof |
| `08f-privacy-and-comparison.tex` | lemma | The first message reveals every partial evaluation | `lem:dpr:leaks-partials` | `ZKDPR.leaks_partials` | complete paper proof |
| `08f-privacy-and-comparison.tex` | theorem | Perfect two-witness distinction from the first message | `thm:dpr:not-zk` | `ZKDPR.not_zk` | complete paper proof |
| `08f-privacy-and-comparison.tex` | definition | Masked field-column interface | `def:dpr:masked-column-interface` | `ZKDPR.masked_column_interface` | typed definition |
| `08f-privacy-and-comparison.tex` | lemma | The basic masked column view does not distinguish | `lem:dpr:masked-column-uniform` | `ZKDPR.masked_column_uniform` | complete paper proof |
| `08f-privacy-and-comparison.tex` | lemma | Revealing the full hidden correction reverses the mask | `lem:dpr:masked-correction-reveal` | `ZKDPR.masked_correction_reveal` | complete paper proof |
| `08f-privacy-and-comparison.tex` | proposition | The two protocol routes are distinct | `prop:dpr:routes-distinct` | `ZKDPR.routes_distinct` | complete paper proof |
| `08g-interfaces.tex` | definition | The three proof-system layers | `def:dpr:layers` | `ZKDPR.layers` | typed definition |
| `08g-interfaces.tex` | lemma | No increase in the packed Boolean table size | `lem:dpr:table-size` | `ZKDPR.table_size` | complete paper proof |
| `08g-interfaces.tex` | lemma | Message types and sumcheck round count | `lem:dpr:round-count` | `ZKDPR.round_count` | complete paper proof |
| `08g-interfaces.tex` | definition | Chapter 8 Lean certification contract | `def:dpr:lean-contract` | `ZKDPR.lean_contract` | typed definition |

## Lean module order

1. `ZKDPR/TensorRing.lean` — tensor product $A=L\otimes_{\mathbb F_2}L$, two embeddings, multiplication map, left-$L$ column basis, non-injectivity of multiplication.
2. `ZKDPR/PackedEvaluation.lean` — binary witness packing, $T'$, $φ1(T')(φ0(r_{hi}))$, exact columns, contraction, degree-two sumcheck summand.
3. `ZKDPR/RingRootBound.lean` — factor theorem over a commutative ring, units of the embedded field, nonzero polynomial root bound at embedded challenges.
4. `ZKDPR/TensorSumcheck.lean` — true partial sums, causal challenges, false-to-true transition, $2h/|L|$ bound.
5. `ZKDPR/Compiler.lean` — typed original Construction 4.1 and the abstract underlying large-field evaluation interface.
6. `ZKDPR/CompilerSoundness.lean` — perfect completeness, lossless extraction from packed $T'$, conditional bound $2h/|L|+\epsilon_{eval}$.
7. `ZKDPR/PrivacyObstruction.lean` — recovery of unmasked partial evaluations from $S_0$, explicit same-evaluation two-witness distinguishing theorem.
8. `ZKDPR/Interfaces.lean` — packed size, message count, and exact security/zero-knowledge boundaries.

## Source provenance and known discrepancies

- **Primary reference:** Diamond and Posen, *Polylogarithmic Proofs for Multilinears over Binary Towers*, ePrint 2024/504, §4, Construction 4.1; Theorems 4.2 and 4.4; Lemma 4.5.
- Chapter 8 reconstructs the **original unmasked** tensor-algebra compiler specialized to ground field $ℝ_2$. The preceding Chapter 7 constructs a **distinct masked affine/traces verification interface**; the two soundness statements are not interchangeable.
- Earlier Diamond 2025/1015 treats large-field PCS zero knowledge but explicitly not ring switching; Kochergin 2026/2754 and Frigo–shelat 2026/2770 discuss subsequent binary-field masking methods.
- The soundness theorem in this chapter assumes a fixed committed packed polynomial $T'$ and an external large-field evaluation error $\epsilon_{eval}$; it does not reproduce the original IOP emulator/extractor or a composed ZK simulator.
- The unmasked tensor message leaks every partial evaluation; an explicit two-witness test has statistical distance one.

## Exact proof target

```text
A := L ⊗[F₂] L
φ₀(a) := a ⊗ 1
φ₁(a) := 1 ⊗ a
S := φ₁(T′)(φ₀(r_hi))
Col(S)_v = Σ_j eq(j,r_hi) * w_(v,j)
y_w = Σ_v eq(v,r_lo) * Col(S)_v
H(X) := φ₁(T′)(X) * eq(φ₀(r_hi),X)
Σ_{j ∈ {0,1}^h} H(j) = S
for P ≠ 0 ∈ A[X], deg(P) ≤ d:
    Pr_{z←L}[P(φ₁(z))=0] ≤ d/|L|
false-claim accept ≤ 2*h/|L| + ε_eval
```

## Remaining commitments

Machine-checked Lean proofs, a concrete commitment-binding and large-field evaluator, a real-world adaptive/verifier query game, and joint zero-knowledge simulation are **not** supplied by Chapter 8's algebraic work. They remain separate proof obligations.
