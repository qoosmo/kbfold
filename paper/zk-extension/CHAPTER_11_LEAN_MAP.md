# Chapter 11 — Malicious-Verifier Zero Knowledge and Temporal Extraction

**Paper audit:** 56 separately labeled definitions/results across eight sections: 16 definitions and **40 complete mathematical paper proofs**. Every non-definition statement has a matched proof environment. No new Chapter 11 declaration is Lean 4 certified.

## Statement-by-statement map

| Source | Kind | Statement | LaTeX label | Proposed Lean declaration | Status |
|---|---|---|---|---|---|
| `11a-bit-challenge.tex` | definition | One-bit OR mini-proof | `def:mv:mini` | `ZKMV.mini` | typed model |
| `11a-bit-challenge.tex` | lemma | Perfect completeness of the mini-proof | `lem:mv:mini-complete` | `ZKMV.mini_complete` | paper proof |
| `11a-bit-challenge.tex` | definition | Schedule-respecting malicious verifier | `def:mv:verifier` | `ZKMV.verifier` | typed model |
| `11a-bit-challenge.tex` | definition | One-step black-box rewinding | `def:mv:rewind` | `ZKMV.rewind` | typed model |
| `11a-bit-challenge.tex` | lemma | A fixed statement admits a known witness in the honest case | `lem:mv:honest-witness` | `ZKMV.honest_witness` | paper proof |
| `11b-fixed-challenge.tex` | definition | Fixed-bit OR transcript simulator | `def:mv:fixed-sim` | `ZKMV.fixed_sim` | typed model |
| `11b-fixed-challenge.tex` | lemma | The simulator always satisfies the verifier equations | `lem:mv:fixed-accepts` | `ZKMV.fixed_accepts` | paper proof |
| `11b-fixed-challenge.tex` | lemma | Honest local challenges are uniform subject to their sum | `lem:mv:local-hyperplane` | `ZKMV.local_hyperplane` | paper proof |
| `11b-fixed-challenge.tex` | lemma | Honest responses are independent uniforms given challenges | `lem:mv:responses` | `ZKMV.responses` | paper proof |
| `11b-fixed-challenge.tex` | theorem | Perfect simulation conditional on any fixed challenge | `thm:mv:fixed-perfect` | `ZKMV.fixed_perfect` | paper proof |
| `11b-fixed-challenge.tex` | lemma | First message is challenge-independent | `lem:mv:first-uniform` | `ZKMV.first_uniform` | paper proof |
| `11b-fixed-challenge.tex` | corollary | Fixed-bit response simulation conditioned on $T$ | `cor:mv:conditional-response` | `ZKMV.conditional_response` | paper proof |
| `11c-malicious-simulator.tex` | definition | Balanced one-bit rewinding simulator | `def:mv:balanced-sim` | `ZKMV.balanced_sim` | typed model |
| `11c-malicious-simulator.tex` | lemma | Every trial is selected with probability one half | `lem:mv:half` | `ZKMV.half` | paper proof |
| `11c-malicious-simulator.tex` | lemma | Expected trial count | `lem:mv:expected-two` | `ZKMV.expected_two` | paper proof |
| `11c-malicious-simulator.tex` | lemma | Balanced selection preserves the real first-message law | `lem:mv:preserve-first` | `ZKMV.preserve_first` | paper proof |
| `11c-malicious-simulator.tex` | lemma | A selected accepting response has the real conditional law | `lem:mv:real-response` | `ZKMV.real_response` | paper proof |
| `11c-malicious-simulator.tex` | theorem | Perfect malicious-verifier zero knowledge for one mini-proof | `thm:mv:one-perfect` | `ZKMV.one_perfect` | paper proof |
| `11c-malicious-simulator.tex` | lemma | Why unconditional acceptance of simulated aborts is biased | `lem:mv:abort-bias` | `ZKMV.abort_bias` | paper proof |
| `11d-sequential-composition.tex` | definition | Sequential amplification parameter | `def:mv:repeat` | `ZKMV.repeat` | typed model |
| `11d-sequential-composition.tex` | lemma | Sequential composition preserves honest completeness | `lem:mv:repeat-complete` | `ZKMV.repeat_complete` | paper proof |
| `11d-sequential-composition.tex` | lemma | Sequential simulator cost | `lem:mv:repeat-cost` | `ZKMV.repeat_cost` | paper proof |
| `11d-sequential-composition.tex` | theorem | Perfect simulation of sequential OR statements | `thm:mv:repeat-perfect` | `ZKMV.repeat_perfect` | paper proof |
| `11d-sequential-composition.tex` | definition | Chapter 11 concrete affine protocol | `def:mv:affine-protocol` | `ZKMV.affine_protocol` | typed model |
| `11d-sequential-composition.tex` | theorem | Perfect expected-time malicious-verifier ZK of the affine transcript | `thm:mv:affine-mvzk` | `ZKMV.affine_mvzk` | paper proof |
| `11d-sequential-composition.tex` | definition | Bounded-retry simulator | `def:mv:truncated` | `ZKMV.truncated` | typed model |
| `11d-sequential-composition.tex` | theorem | Strict polynomial time with negligible statistical error | `thm:mv:truncated` | `ZKMV.truncated` | paper proof |
| `11e-forking.tex` | definition | Resettable fixed-statement prover | `def:mv:reset-prover` | `ZKMV.reset_prover` | typed model |
| `11e-forking.tex` | definition | Accepting challenge set | `def:mv:accepting-set` | `ZKMV.accepting_set` | typed model |
| `11e-forking.tex` | lemma | Earliest difference yields one OR fork | `lem:mv:earliest` | `ZKMV.earliest` | paper proof |
| `11e-forking.tex` | theorem | Combinatorial knowledge extraction from two accepting runs | `thm:mv:two-run-extract` | `ZKMV.two_run_extract` | paper proof |
| `11e-forking.tex` | lemma | Exact two-run forking probability | `lem:mv:fork-prob` | `ZKMV.fork_prob` | paper proof |
| `11e-forking.tex` | theorem | Randomized-prover two-run forking bound | `thm:mv:fork-average` | `ZKMV.fork_average` | paper proof |
| `11e-forking.tex` | corollary | Knowledge-error dichotomy | `cor:mv:knowledge-error` | `ZKMV.knowledge_error` | paper proof |
| `11e-forking.tex` | lemma | Why a single global $\kappa$-bit guess is costly | `lem:mv:parallel-cost` | `ZKMV.parallel_cost` | paper proof |
| `11f-temporal-extraction.tex` | definition | Pre-challenge registration boundary | `def:mv:boundary` | `ZKMV.boundary` | typed model |
| `11f-temporal-extraction.tex` | lemma | A local reset occurs before the protected challenge | `lem:mv:temporal-local` | `ZKMV.temporal_local` | paper proof |
| `11f-temporal-extraction.tex` | theorem | Stand-alone early extraction with quantitative success | `thm:mv:standalone-early` | `ZKMV.standalone_early` | paper proof |
| `11f-temporal-extraction.tex` | lemma | At most one successful challenge path without a fork | `lem:mv:single-leaf` | `ZKMV.single_leaf` | paper proof |
| `11f-temporal-extraction.tex` | lemma | False parity plus a fork solves setup discrete log | `lem:mv:false-parity-fork` | `ZKMV.false_parity_fork` | paper proof |
| `11f-temporal-extraction.tex` | theorem | Quantitative soundness for a false parity with known true opening | `thm:mv:false-parity-bound` | `ZKMV.false_parity_bound` | paper proof |
| `11f-temporal-extraction.tex` | lemma | Different first messages do not imply extractability | `lem:mv:fork-needs-same-first` | `ZKMV.fork_needs_same_first` | paper proof |
| `11f-temporal-extraction.tex` | definition | Global temporal coupling obligation | `def:mv:global-coupling` | `ZKMV.global_coupling` | typed model |
| `11f-temporal-extraction.tex` | proposition | Local extraction does not yet prove global coupling | `prop:mv:coupling-open` | `ZKMV.coupling_open` | paper proof |
| `11g-security-boundaries.tex` | definition | Per-proof conditional false-parity bound | `def:mv:row-error` | `ZKMV.row_error` | typed model |
| `11g-security-boundaries.tex` | lemma | Union bound for false accepted parity rows | `lem:mv:row-union` | `ZKMV.row_union` | paper proof |
| `11g-security-boundaries.tex` | definition | Global extraction error | `def:mv:coupling-error` | `ZKMV.coupling_error` | typed model |
| `11g-security-boundaries.tex` | theorem | Conditional soundness of the sequential-bit compiler | `thm:mv:conditional-sound` | `ZKMV.conditional_sound` | paper proof |
| `11g-security-boundaries.tex` | lemma | Malicious-verifier ZK does not depend on uniform outer challenges | `lem:mv:outer-adaptive` | `ZKMV.outer_adaptive` | paper proof |
| `11g-security-boundaries.tex` | theorem | An unmasked authenticated opening defeats witness privacy | `thm:mv:raw-oracle-leak` | `ZKMV.raw_oracle_leak` | paper proof |
| `11g-security-boundaries.tex` | proposition | The Chapter 11 transcript result does not certify original KBFold | `prop:mv:not-kbfold` | `ZKMV.not_kbfold` | paper proof |
| `11h-cost-and-roadmap.tex` | definition | Compiled proof counts | `def:mv:proof-count` | `ZKMV.proof_count` | typed model |
| `11h-cost-and-roadmap.tex` | lemma | Exact mini-proof count | `lem:mv:proof-count` | `ZKMV.proof_count` | paper proof |
| `11h-cost-and-roadmap.tex` | lemma | Expected and bounded simulator costs | `lem:mv:simulation-cost` | `ZKMV.simulation_cost` | paper proof |
| `11h-cost-and-roadmap.tex` | proposition | A security-efficiency tradeoff | `prop:mv:tradeoff` | `ZKMV.tradeoff` | paper proof |
| `11h-cost-and-roadmap.tex` | definition | Lean certification graph | `def:mv:lean-graph` | `ZKMV.lean_graph` | typed model |

## Lean 4 certification plan

1. `ZKMV/OneBitOR.lean` — one-bit OR mini-proof, challenge ranges, completeness.
2. `ZKMV/FixedChallenge.lean` — uniform local challenge hyperplane, independent uniform responses, fixed-$e$ transcript simulator.
3. `ZKMV/BalancedRewinding.lean` — malicious bit challenge and abort model, corrected abort acceptance, exact conditional laws, geometric expected 2 trials.
4. `ZKMV/SequentialSimulation.lean` — induction over mini-proofs and the entire one-opening affine proof transcript, outer causal challenge dependence, truncated simulator bound `M*2^(-R)`.
5. `ZKMV/ForkingTree.lean` — accepting challenge strings, earliest differing bit, same-first-message extractor, exact forking probability `p(p-2^(-kappa))`.
6. `ZKMV/ForkingAverage.lean` — randomized prover bound `eps(eps-2^(-kappa))` and polynomial-time local witness extraction.
7. `ZKMV/TemporalLocal.lean` — before-theta or before-z registration, stand-alone temporal extraction and false-parity discrete-log reduction.
8. `ZKMV/ConditionalOuterSoundness.lean` — conditional field/commitment timing, per-false-parity row error, full union-bound statement.
9. `ZKMV/Cost.lean` — $M=\kappa(B+Q)$ one-bit proofs, expected rewinding and explicit nonsuccinctness.
10. **Open:** `ZKMV/GlobalTemporalCoupling.lean` — one efficient extractor preserving the same accepted transcript across all dependent pre/post-outer-challenge statements. This is **not proved**.
11. **Open:** KBFold authenticated oracle and post-quantum composition, which is a different original odd-characteristic protocol.

## Security guarantees and exclusions

**Proved for classical, schedule-respecting, rewindable verifiers:**
- The fixed-bit OR transcript is perfectly simulatable for either challenge in ${0,1}$.
- The balanced trial simulator matches the malicious verifier's full one-mini-proof view, even if it aborts as a function of the first message. Accepting every simulated abort unconditionally would bias the abort distribution.
- Sequential one-bit repetition gives **perfect expected-polynomial-time malicious-verifier zero knowledge** for the *one-opening affine transcript*, including Pedersen commitments and public Ring Switching messages, with arbitrary causal **outer** challenges.
- The strict-polynomial truncated simulator has statistical simulation error at most $M2^{-R}$.
- Two different accepted challenge strings under an identical reset prover random tape give an OR opening. The quantitative two-run probability is at least $\max\{0,\varepsilon(\varepsilon-2^{-\kappa})\}$.
- If a row's true bit openings are already known and its target parity is false, that fork recovers the forbidden Pedersen setup logarithm, giving $\varepsilon\le 2^{-\kappa}+\sqrt{\delta_{\rm DL}}$.
- Pre-outer-challenge **stand-alone** extraction follows when registration proofs occur entirely before the outer challenge.

**Conditional / unresolved:**
- The single global temporal extraction coupling with challenge timing and a preserved accepted transcript remains open. The stand-alone two-run theorem does not imply it.
- Full false-claim soundness adds $\varepsilon_{\rm couple}$, $Q\eta_{\rm row}$ and $\varepsilon_{\rm oracle}$ to the ideal algebraic $(\ell+n)/2^n$ bound.
- The simulator does not cover actual KBFold commitment roots, Reed--Solomon/FRI authentication paths, reused masks, the odd-characteristic word-fold, quantum verifiers or QROM proofs.
- The raw Pedersen/Schnorr construction is nonsuccinct, classical discrete-log based, and not post-quantum.

## Primary sources

- Schnorr (1991); Cramer--Damg{å}rd--Schoenmakers (1994); Goldreich, *Foundations of Cryptography*, Volume 1 (2001); Pedersen (1991).
- The exact Stage 11 security boundary refers to KBFold Chapter 10's affine compiler and Chapter 9's public-core simulator.

## Reproducible audit

Run `sh audit/RUN.sh`. The new `audit/malicious_sigma.rs` uses an intentionally insecure prime-order toy group only to **exhaustively compare** fixed-bit transcript laws, the balanced malicious-verifier simulation including aborts, and the exact two-run forking probability. These regression tests are not cryptographic security proofs.
