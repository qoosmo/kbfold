# Chapter 3: formal theorem and Lean 4 map

**Status at 7 November 2026.** Chapter 3 is written with fully stated definitions and full paper proofs for the algebraic lemmas and theorems. None of the *new* chapter-specific Lean declarations below has been machine checked yet. The Lean names are proposals, not claims of existing code.

This chapter contains **62 numbered definitions/results**. Its new results are split into small statements instead of one large security theorem. The same mathematical definitions should be represented as finite types, probability mass functions, linear maps and time-ordered oracle strategies in Lean.

| Type | Mathematical statement | LaTeX label | Proposed Lean 4 declaration | Status |
|---|---|---|---|---|
| definition | Finite probability distribution | `def:security:distribution` | `ZKSecurity.distribution` | defined |
| definition | Total variation distance | `def:security:tv` | `ZKSecurity.tv` | defined |
| lemma | Range and symmetry | `lem:security:tv-range` | `ZKSecurity.tv_range` | paper proof |
| lemma | Triangle inequality | `lem:security:tv-triangle` | `ZKSecurity.tv_triangle` | paper proof |
| lemma | Event characterization and separating events | `lem:security:events` | `ZKSecurity.events` | paper proof |
| definition | Markov kernel and pushforward | `def:security:kernel` | `ZKSecurity.kernel` | defined |
| lemma | Data processing | `lem:security:data-processing` | `ZKSecurity.data_processing` | paper proof |
| corollary | Projection does not improve distinguishing | `cor:security:projection` | `ZKSecurity.projection` | paper proof |
| lemma | Convexity under a shared mixing distribution | `lem:security:mixture` | `ZKSecurity.mixture` | paper proof |
| lemma | Stepwise hybrid bound | `lem:security:hybrid` | `ZKSecurity.hybrid` | paper proof |
| definition | Evaluation domain and initial oracle | `def:security:domain` | `ZKSecurity.domain` | defined |
| definition | Public-coin IOP transcript | `def:security:iop` | `ZKSecurity.iop` | defined |
| definition | Timing-respecting prover | `def:security:causal-prover` | `ZKSecurity.causal_prover` | defined |
| lemma | The honest transcript distribution is defined | `lem:security:finite-transcript` | `ZKSecurity.finite_transcript` | paper proof |
| definition | Adaptive verifier and query bound | `def:security:adaptive` | `ZKSecurity.adaptive` | defined |
| lemma | Finite decision-tree representation | `lem:security:decision-tree` | `ZKSecurity.decision_tree` | paper proof |
| definition | Verifier's view | `def:security:view` | `ZKSecurity.view` | defined |
| definition | Abstract oracle commitment | `def:security:commitment` | `ZKSecurity.commitment` | defined |
| definition | Coordinate-binding experiment | `def:security:binding` | `ZKSecurity.binding` | defined |
| definition | Standalone commitment hiding | `def:security:commit-hiding` | `ZKSecurity.commit_hiding` | defined |
| definition | Kernel encoding as a word | `def:security:encoding` | `ZKSecurity.encoding` | defined |
| lemma | Injectivity of kernel encoding | `lem:security:encoding-injective` | `ZKSecurity.encoding_injective` | paper proof |
| definition | Hamming distance | `def:security:hamming` | `ZKSecurity.hamming` | defined |
| lemma | Triangle inequality for Hamming distance | `lem:security:hamming-triangle` | `ZKSecurity.hamming_triangle` | paper proof |
| theorem | Reed--Solomon minimum distance | `thm:security:rs-distance` | `ZKSecurity.rs_distance` | paper proof |
| definition | Exact evaluation relation | `def:security:exactrel` | `ZKSecurity.exactrel` | defined |
| definition | Proximity evaluation relation | `def:security:proxrel` | `ZKSecurity.proxrel` | defined |
| lemma | Uniqueness of a nearby codeword | `lem:security:unique-near` | `ZKSecurity.unique_near` | paper proof |
| corollary | At most one nearby evaluation value | `cor:security:unique-value` | `ZKSecurity.unique_value` | paper proof |
| definition | Oracle evaluation soundness | `def:security:eval-sound` | `ZKSecurity.eval_sound` | defined |
| definition | Perfect completeness for kernel evaluation | `def:security:complete` | `ZKSecurity.complete` | defined |
| definition | False-statement acceptance experiment | `def:security:bad-proof` | `ZKSecurity.bad_proof` | defined |
| lemma | Deterministic-prover reduction | `lem:security:randomized-prover` | `ZKSecurity.randomized_prover` | paper proof |
| definition | Doomed partial transcript | `def:security:doomed` | `ZKSecurity.doomed` | defined |
| lemma | First escape is necessary for acceptance | `lem:security:first-escape` | `ZKSecurity.first_escape` | paper proof |
| theorem | Round-by-round implies overall soundness | `thm:security:rbr-sound` | `ZKSecurity.rbr_sound` | paper proof |
| definition | Round-by-round knowledge witness | `def:security:rbr-knowledge` | `ZKSecurity.rbr_knowledge` | defined |
| theorem | Knowledge certificate implies witness or bounded acceptance | `thm:security:knowledge-overall` | `ZKSecurity.knowledge_overall` | paper proof |
| definition | Witness-dependent real view | `def:security:real` | `ZKSecurity.real` | defined |
| definition | Statistical zero knowledge for a fixed evaluation point | `def:security:szk` | `ZKSecurity.szk` | defined |
| definition | Computational distinguishing advantage | `def:security:computational` | `ZKSecurity.computational` | defined |
| lemma | Two-witness closeness is necessary | `lem:security:two-witness` | `ZKSecurity.two_witness` | paper proof |
| lemma | A public-message projection remains simulatable | `lem:security:message-projection` | `ZKSecurity.message_projection` | paper proof |
| theorem | One-query leakage of an unmasked KBFold oracle | `thm:security:unmasked-obstruction` | `ZKSecurity.unmasked_obstruction` | paper proof |
| lemma | Reusing one pad leaks a difference | `lem:security:pad-reuse` | `ZKSecurity.pad_reuse` | paper proof |
| definition | Linear masking experiment | `def:security:linear-mask` | `ZKSecurity.linear_mask` | defined |
| lemma | Uniformity on an affine coset | `lem:security:affine-uniform` | `ZKSecurity.affine_uniform` | paper proof |
| lemma | Exact distinguishing criterion for linear observations | `lem:security:coset-criterion` | `ZKSecurity.coset_criterion` | paper proof |
| lemma | Conditional uniformity after linear queries | `lem:security:conditioned-mask` | `ZKSecurity.conditioned_mask` | paper proof |
| corollary | One more adaptive linear oracle query | `cor:security:adaptive-next` | `ZKSecurity.adaptive_next` | paper proof |
| lemma | Evaluation masks at arbitrary distinct points | `lem:security:lagrange` | `ZKSecurity.lagrange` | paper proof |
| corollary | Uniform masking of a bounded set of evaluation queries | `cor:security:q-query-uniform` | `ZKSecurity.q_query_uniform` | paper proof |
| definition | Ideal evaluation functionality | `def:security:ideal-eval` | `ZKSecurity.ideal_eval` | defined |
| definition | Online real evaluation game | `def:security:online-real` | `ZKSecurity.online_real` | defined |
| definition | Online ideal evaluation game | `def:security:online-ideal` | `ZKSecurity.online_ideal` | defined |
| definition | Online zero knowledge | `def:security:online-zk` | `ZKSecurity.online_zk` | defined |
| lemma | Stepwise online simulation suffices | `lem:security:online-hybrid` | `ZKSecurity.online_hybrid` | paper proof |
| definition | Unmasked KBFold transcript components | `def:security:kbfold-transcript` | `ZKSecurity.kbfold_transcript` | defined |
| lemma | KBFold round-sum equality | `lem:security:kbfold-roundsum` | `ZKSecurity.kbfold_roundsum` | paper proof |
| lemma | KBFold round-polynomial degree | `lem:security:kbfold-rounddegree` | `ZKSecurity.kbfold_rounddegree` | paper proof |
| theorem | A naive high-degree mask does not preserve final closure | `thm:security:naive-closure` | `ZKSecurity.naive_closure` | paper proof |
| definition | ZK-KBFold certification obligations | `def:security:obligation-ledger` | `ZKSecurity.obligation_ledger` | defined |

## Suggested modules (in dependency order)

1. `ZKSecurity/FiniteProbability.lean` — finite distributions, total variation, data processing, hybrid.
2. `ZKSecurity/OracleGame.lean` — typed oracles, causal strategies, verifier views.
3. `ZKSecurity/Commitment.lean` — commitment/opening/check interfaces, correctness/binding/hiding definitions.
4. `ZKSecurity/EvaluationRelation.lean` — kernel encoding, Reed--Solomon minimum distance, unique decoding radius.
5. `ZKSecurity/RoundByRound.lean` — doomed sets and knowledge-extraction implication.
6. `ZKSecurity/StatisticalZK.lean` — simulation game, projection, two-witness criterion, one-query obstruction.
7. `ZKSecurity/MaskSubspace.lean` — uniform affine cosets, adaptive conditional distributions.
8. `ZKSecurity/OnlineZK.lean` — online commitment-before-point experiment, authenticated views, hybrid.
9. `ZKSecurity/HighDegreeClosure.lean` — original KBFold protocol round equations and explicit residual-mask counterexample.

## Imported facts and existing results

- The Boolean kernel basis, multilinear extension, and normalized fold dictionary are proved earlier in this manuscript and substantially overlap with existing `lean/KBFold/Kernel.lean` and `lean/KBFold/WordFold.lean`.
- The univariate root-count bound and Schwartz--Zippel are proved in Chapter 2. Lean can use existing Mathlib polynomial root-count and measure lemmas where their hypotheses match.
- This chapter does **not** prove the new commitment scheme's implementation security, the final zero-knowledge theorem, or an unproven QROM compiler result.

## Cryptographic research obligations

A future `zk_kbfold_security` theorem requires a concrete prover, verifier, commitment scheme, masking distributions and an online simulator, and proofs of completeness, soundness and online zero knowledge. Statements about source-level definitions alone are not such a theorem.
