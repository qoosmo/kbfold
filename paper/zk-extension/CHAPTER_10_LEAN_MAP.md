# Chapter 10 — Commitment and Affine-Proof Realization: Lean 4 Map

**Audit:** 57 labeled definitions/results in 8 sections, including **39 complete paper proofs** and 18 typed definitions. Every non-definition statement has a proof environment. None of the chapter's new declarations is Lean certified.

| Section | Kind | Statement | LaTeX label | Lean target | Status |
|---|---|---|---|---|---|
| `10a-binary-affine.tex` | definition | Field-variable bit representation | `def:realize:bits` | `ZKAffine.bits` | typed model |
| `10a-binary-affine.tex` | definition | Public binary coefficient matrix | `def:realize:matrix` | `ZKAffine.matrix` | typed model |
| `10a-binary-affine.tex` | lemma | Coordinates of a publicly scaled element | `lem:realize:scaled` | `ZKAffine.scaled` | complete paper proof |
| `10a-binary-affine.tex` | theorem | Exact affine-to-parity equivalence | `thm:realize:affine-to-parity` | `ZKAffine.affine_to_parity` | complete paper proof |
| `10a-binary-affine.tex` | corollary | No multiplication of two hidden field elements | `cor:realize:linear-gates` | `ZKAffine.linear_gates` | complete paper proof |
| `10a-binary-affine.tex` | lemma | Row size bound | `lem:realize:row-weight` | `ZKAffine.row_weight` | complete paper proof |
| `10b-pedersen.tex` | definition | Prime-order commitment parameters | `def:realize:group` | `ZKAffine.group` | typed model |
| `10b-pedersen.tex` | definition | Pedersen commitment to a binary coordinate | `def:realize:commit` | `ZKAffine.commit` | typed model |
| `10b-pedersen.tex` | lemma | Exact perfect hiding | `lem:realize:hiding` | `ZKAffine.hiding` | complete paper proof |
| `10b-pedersen.tex` | lemma | Two openings recover the forbidden setup logarithm | `lem:realize:binding-reduction` | `ZKAffine.binding_reduction` | complete paper proof |
| `10b-pedersen.tex` | theorem | Computational binding for bits | `thm:realize:binding` | `ZKAffine.binding` | complete paper proof |
| `10b-pedersen.tex` | definition | Aggregating commitments | `def:realize:product` | `ZKAffine.product` | typed model |
| `10b-pedersen.tex` | lemma | Exact aggregate opening | `lem:realize:aggregate` | `ZKAffine.aggregate` | complete paper proof |
| `10b-pedersen.tex` | lemma | Why naive XOR homomorphism fails | `lem:realize:no-xor` | `ZKAffine.no_xor` | complete paper proof |
| `10c-or-schnorr.tex` | definition | Schnorr relation | `def:realize:schnorr` | `ZKAffine.schnorr` | typed model |
| `10c-or-schnorr.tex` | lemma | Schnorr completeness | `lem:realize:schnorr-complete` | `ZKAffine.schnorr_complete` | complete paper proof |
| `10c-or-schnorr.tex` | lemma | Two Schnorr transcripts extract the logarithm | `lem:realize:schnorr-extract` | `ZKAffine.schnorr_extract` | complete paper proof |
| `10c-or-schnorr.tex` | lemma | Perfect honest-verifier Schnorr simulation | `lem:realize:schnorr-hvzk` | `ZKAffine.schnorr_hvzk` | complete paper proof |
| `10c-or-schnorr.tex` | definition | Schnorr OR proof for a finite candidate set | `def:realize:or` | `ZKAffine.or` | typed model |
| `10c-or-schnorr.tex` | lemma | OR-proof perfect completeness | `lem:realize:or-complete` | `ZKAffine.or_complete` | complete paper proof |
| `10c-or-schnorr.tex` | theorem | OR-proof perfect honest-verifier zero knowledge | `thm:realize:or-hvzk` | `ZKAffine.or_hvzk` | complete paper proof |
| `10c-or-schnorr.tex` | theorem | OR-proof special soundness | `thm:realize:or-extract` | `ZKAffine.or_extract` | complete paper proof |
| `10d-parity.tex` | definition | Parity-compatible integer openings | `def:realize:candidates` | `ZKAffine.candidates` | typed model |
| `10d-parity.tex` | lemma | Correct integer sum lies in the permitted set | `lem:realize:correct-candidate` | `ZKAffine.correct_candidate` | complete paper proof |
| `10d-parity.tex` | definition | Concrete parity proof | `def:realize:parity-proof` | `ZKAffine.parity_proof` | typed model |
| `10d-parity.tex` | theorem | Perfect completeness of the parity compiler | `thm:realize:parity-complete` | `ZKAffine.parity_complete` | complete paper proof |
| `10d-parity.tex` | lemma | An incorrect parity gives two different aggregate openings | `lem:realize:parity-equivocation` | `ZKAffine.parity_equivocation` | complete paper proof |
| `10d-parity.tex` | theorem | False parity reveals the setup logarithm | `thm:realize:parity-binding` | `ZKAffine.parity_binding` | complete paper proof |
| `10d-parity.tex` | theorem | Perfect honest-verifier privacy of parity proofs | `thm:realize:parity-hvzk` | `ZKAffine.parity_hvzk` | complete paper proof |
| `10d-parity.tex` | corollary | Exact empty-row handling | `cor:realize:empty-row` | `ZKAffine.empty_row` | complete paper proof |
| `10e-field-affine-compiler.tex` | definition | Bit-committed field variables | `def:realize:field-commit` | `ZKAffine.field_commit` | typed model |
| `10e-field-affine-compiler.tex` | lemma | Registered coordinates reconstruct one field element | `lem:realize:field-reconstruct` | `ZKAffine.field_reconstruct` | complete paper proof |
| `10e-field-affine-compiler.tex` | definition | Affine proof compiler | `def:realize:affine-compiler` | `ZKAffine.affine_compiler` | typed model |
| `10e-field-affine-compiler.tex` | lemma | All affine row statements are publicly computable | `lem:realize:rows-public` | `ZKAffine.rows_public` | complete paper proof |
| `10e-field-affine-compiler.tex` | theorem | Perfect completeness of the field-affine compiler | `thm:realize:compiler-complete` | `ZKAffine.compiler_complete` | complete paper proof |
| `10e-field-affine-compiler.tex` | theorem | Extracted field-affine correctness | `thm:realize:compiler-extract` | `ZKAffine.compiler_extract` | complete paper proof |
| `10e-field-affine-compiler.tex` | lemma | Faithful compilation of the Chapter 9 checker | `lem:realize:chapter9-affine` | `ZKAffine.chapter9_affine` | complete paper proof |
| `10e-field-affine-compiler.tex` | lemma | Packed-column equality is also field affine in bits | `lem:realize:packing-link` | `ZKAffine.packing_link` | complete paper proof |
| `10f-honest-verifier-zk.tex` | definition | Restricted honest-sigma-verifier model | `def:realize:hv-model` | `ZKAffine.hv_model` | typed model |
| `10f-honest-verifier-zk.tex` | lemma | Fresh commitments are conditionally uniform | `lem:realize:conditional-commit` | `ZKAffine.conditional_commit` | complete paper proof |
| `10f-honest-verifier-zk.tex` | lemma | A prescribed OR proof has a witness-free conditional simulator | `lem:realize:conditional-or` | `ZKAffine.conditional_or` | complete paper proof |
| `10f-honest-verifier-zk.tex` | definition | Concrete honest-verifier simulator | `def:realize:hv-sim` | `ZKAffine.hv_sim` | typed model |
| `10f-honest-verifier-zk.tex` | theorem | Perfect honest-verifier ZK of the concrete affine transcript | `thm:realize:full-hvzk` | `ZKAffine.full_hvzk` | complete paper proof |
| `10f-honest-verifier-zk.tex` | corollary | No witness-dependent commitment-token distribution | `cor:realize:tokens` | `ZKAffine.tokens` | complete paper proof |
| `10g-extraction-and-boundaries.tex` | definition | Extraction-before-challenge contract | `def:realize:early-extract` | `ZKAffine.early_extract` | typed model |
| `10g-extraction-and-boundaries.tex` | lemma | Accepted parity equations are valid under extracted consistency | `lem:realize:extracted-correct` | `ZKAffine.extracted_correct` | complete paper proof |
| `10g-extraction-and-boundaries.tex` | theorem | Conditional soundness of the explicit bit-commitment compiler | `thm:realize:outer-sound` | `ZKAffine.outer_sound` | complete paper proof |
| `10g-extraction-and-boundaries.tex` | lemma | Multi-statement extraction cannot be silently assumed | `lem:realize:extract-needs-proof` | `ZKAffine.extract_needs_proof` | complete paper proof |
| `10g-extraction-and-boundaries.tex` | definition | Malicious sigma-verifier security target | `def:realize:mv-target` | `ZKAffine.mv_target` | typed model |
| `10g-extraction-and-boundaries.tex` | proposition | The proven HVZK simulator does not discharge the malicious target | `prop:realize:hv-not-mv` | `ZKAffine.hv_not_mv` | complete paper proof |
| `10g-extraction-and-boundaries.tex` | definition | Concrete ZK compiler obligation | `def:realize:mv-compiler` | `ZKAffine.mv_compiler` | typed model |
| `10h-accounting.tex` | definition | Affine compilation parameters | `def:realize:complexity` | `ZKAffine.complexity` | typed model |
| `10h-accounting.tex` | lemma | Exact bit commitment and parity proof counts | `lem:realize:count` | `ZKAffine.count` | complete paper proof |
| `10h-accounting.tex` | lemma | Linear branch-size upper bound | `lem:realize:branch-upper` | `ZKAffine.branch_upper` | complete paper proof |
| `10h-accounting.tex` | lemma | Two group elements per branch in a raw OR proof | `lem:realize:or-communication` | `ZKAffine.or_communication` | complete paper proof |
| `10h-accounting.tex` | proposition | Raw compiler overhead | `prop:realize:not-succinct` | `ZKAffine.not_succinct` | complete paper proof |
| `10h-accounting.tex` | definition | Chapter 10 Lean module contract | `def:realize:lean-map` | `ZKAffine.lean_map` | typed model |

## Certification modules in dependency order

1. `ZKAffine/FieldBitMatrices.lean` — arbitrary-public-coefficient affine equations over finite characteristic-two fields become exact binary-coordinate parity systems.
2. `ZKAffine/Pedersen.lean` — cyclic odd-prime-order group, perfect hiding, explicit two-opening discrete-log reduction, integer exponents vs XOR.
3. `ZKAffine/Schnorr.lean` — equations for the basic Schnorr protocol, perfect HVZK, special soundness.
4. `ZKAffine/OrProof.lean` — all $d$ branches of the CDS OR protocol, transcript simulator, extraction.
5. `ZKAffine/Parity.lean` — candidate integer parity sets, bitness proof, aggregate proof, binding and HVZK.
6. `ZKAffine/AffineCompiler.lean` — register field values by binary commitments, public row construction, correct packing link, extracted correctness.
7. `ZKAffine/TranscriptSimulator.lean` — precise honest-sigma-verifier transcript model and perfect conditional-kernel simulation with adaptive outer challenges.
8. `ZKAffine/EarlyExtraction.lean` — explicit multistage extraction contract and conditional outer false-claim bound; not automatically implied by a single OR proof.
9. `ZKAffine/MaliciousVerifierBoundary.lean` — separate malicious sigma-verifier ZK statement, comparison of quantifiers and QROM / post-quantum exclusions.
10. `ZKAffine/Accounting.lean` — bit commitments, row counts, OR branches, asymptotic lack of succinctness.

## Precise security scope

- Group scalar field $𝔽_P$ has **odd** prime characteristic; binary packed field $L$ has characteristic **2**. They are related only through `ZKAffine/FieldBitMatrices`, not through a fictitious field homomorphism.
- Concrete commitments and OR-proofs have perfect completeness, perfect hiding / **honest-verifier** proof simulation, and extraction-based computational binding under classical discrete-logarithm hardness.
- Theorem `thm:realize:full-hvzk` gives perfect simulation for one valid opening when every **inner sigma-proof challenge is independent uniform**; the outer Ring Switching challenges $θ,z$ may be causal/adaptive.
- Theorem `thm:realize:outer-sound` is conditional on **early extraction** of commitments into one fixed field tuple before the relevant outer challenge. Neither Schnorr special soundness nor Pedersen binding alone proves this multistage coupling.
- This construction is **not succinct**, **not post-quantum binding**, and **not full malicious-verifier ZK**, nor does it simulate original KBFold's oracle/Merkle opening transcript.

## Historical sources

- T. P. Pedersen, *Non-Interactive and Information-Theoretic Secure Verifiable Secret Sharing*, CRYPTO 1991 (published LNCS 1992).
- C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*, Journal of Cryptology 4(3), 1991.
- R. Cramer, I. Damgård, B. Schoenmakers, *Proofs of Partial Knowledge and Simplified Design of Witness Hiding Protocols*, CRYPTO 1994.
- Diamond--Posen tensor compiler, KBFold base protocol, Kochergin and Frigo--shelat binary-field ZK masking, as previously cited.

## Regression tests

`audit/affine_sigma.rs` uses an explicitly **insecure toy group** (order 11) for algebraic verification only. It checks exhaustive HVZK transcript distribution equality for two-branch OR proofs, special-soundness extraction, a concrete two-opening collision recovering the setup log, and exhaustive GF(16) affine-to-parity equivalence. These are mathematical regression tests, not security evidence or a cryptographic implementation.
