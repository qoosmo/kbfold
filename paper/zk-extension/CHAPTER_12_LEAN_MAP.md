# Chapter 12 — Global Temporal Extraction and Classical Soundness

**Audit:** 32 formal declarations in five subsections: 11 definitions and **21 complete paper proofs**. The new Chapter 12 theorems are not Lean-certified.

**Scope:** One single-opening, classical, checkpoint-replayable, public-coin implementation of the sequential one-bit OR affine compiler; complete registration and bitness proofs at the required epoch boundaries. External authenticated KBFold oracle security is a named hypothesis.

## Individual theorem/dependency map

| Source | Kind | Title | LaTeX label | Suggested Lean declaration | Status |
|---|---|---|---|---|---|
| `12a-checkpoints.tex` | definition | Three outer epochs | `def:global:epochs` | `ZKGlobal.epochs` | typed interface |
| `12a-checkpoints.tex` | definition | Sequential OR blocks | `def:global:block` | `ZKGlobal.block` | typed interface |
| `12a-checkpoints.tex` | definition | Checkpoint-replay access | `def:global:access` | `ZKGlobal.access` | typed interface |
| `12a-checkpoints.tex` | definition | Main and side executions | `def:global:main` | `ZKGlobal.main` | typed interface |
| `12a-checkpoints.tex` | lemma | Replay preserves the main-path law | `lem:global:main-law` | `ZKGlobal.main_law` | paper proof |
| `12a-checkpoints.tex` | lemma | Protected outer challenges stay independent | `lem:global:outer-uniform` | `ZKGlobal.outer_uniform` | paper proof |
| `12b-online-fork.tex` | definition | Local accepted challenge tree | `def:global:tree` | `ZKGlobal.tree` | typed interface |
| `12b-online-fork.tex` | lemma | Probability of a distinct accepting side string | `lem:global:side-success` | `ZKGlobal.side_success` | paper proof |
| `12b-online-fork.tex` | lemma | Exact failure probability after bounded replay | `lem:global:exact-fail` | `ZKGlobal.exact_fail` | paper proof |
| `12b-online-fork.tex` | lemma | Uniform elementary replay bound | `lem:global:uniform-fail` | `ZKGlobal.uniform_fail` | paper proof |
| `12b-online-fork.tex` | theorem | Per-block online extraction with a preserved main path | `thm:global:one-block` | `ZKGlobal.one_block` | paper proof |
| `12b-online-fork.tex` | corollary | Uniform extraction error over sequential blocks | `cor:global:J-blocks` | `ZKGlobal.J_blocks` | paper proof |
| `12b-online-fork.tex` | lemma | Expected and worst-case replay overhead | `lem:global:runtime` | `ZKGlobal.runtime` | paper proof |
| `12c-global-registry.tex` | definition | Tagged bit-commitment registry | `def:global:registry` | `ZKGlobal.registry` | typed interface |
| `12c-global-registry.tex` | definition | Global checkpoint extractor | `def:global:extractor` | `ZKGlobal.extractor` | typed interface |
| `12c-global-registry.tex` | lemma | A group element has a unique blinding for a fixed bit | `lem:global:unique-r` | `ZKGlobal.unique_r` | paper proof |
| `12c-global-registry.tex` | lemma | Conflicting extracted bits reveal the setup logarithm | `lem:global:tag-conflict` | `ZKGlobal.tag_conflict` | paper proof |
| `12c-global-registry.tex` | lemma | False aggregate parity reveals the setup logarithm | `lem:global:row-conflict` | `ZKGlobal.row_conflict` | paper proof |
| `12c-global-registry.tex` | lemma | Correct parity of every row gives all field-affine equations | `lem:global:all-affine` | `ZKGlobal.all_affine` | paper proof |
| `12c-global-registry.tex` | theorem | Global chronological extraction | `thm:global:chronological` | `ZKGlobal.chronological` | paper proof |
| `12c-global-registry.tex` | corollary | No separately assumed global extractor for this affine compiler | `cor:global:discharged` | `ZKGlobal.discharged` | paper proof |
| `12d-final-soundness.tex` | definition | External authenticated-oracle error | `def:global:oracle-error` | `ZKGlobal.oracle_error` | typed interface |
| `12d-final-soundness.tex` | definition | Forking reduction against the group setup | `def:global:dl-reduction` | `ZKGlobal.dl_reduction` | typed interface |
| `12d-final-soundness.tex` | lemma | A good accepting false claim is an algebraic exception | `lem:global:good-ideal` | `ZKGlobal.good_ideal` | paper proof |
| `12d-final-soundness.tex` | theorem | Explicit finite-replay soundness reduction | `thm:global:finite-sound` | `ZKGlobal.finite_sound` | paper proof |
| `12d-final-soundness.tex` | corollary | Choose replay budget from a claimed cheating advantage | `cor:global:advantage` | `ZKGlobal.advantage` | paper proof |
| `12d-final-soundness.tex` | theorem | Classical computational soundness of the affine component | `thm:global:asymptotic` | `ZKGlobal.asymptotic` | paper proof |
| `12e-protocol-and-handoff.tex` | definition | Checkpoint extractor pseudocode | `def:global:pseudocode` | `ZKGlobal.pseudocode` | typed interface |
| `12e-protocol-and-handoff.tex` | lemma | Every successful replay extracts from the original statement | `lem:global:tag-same` | `ZKGlobal.tag_same` | paper proof |
| `12e-protocol-and-handoff.tex` | lemma | All extracted bit values are registered before use | `lem:global:before-use` | `ZKGlobal.before_use` | paper proof |
| `12e-protocol-and-handoff.tex` | proposition | Polynomial overhead for non-negligible cheating advantage | `prop:global:polynomial` | `ZKGlobal.polynomial` | paper proof |
| `12e-protocol-and-handoff.tex` | definition | Chapter 13 external interface | `def:global:external` | `ZKGlobal.external` | typed interface |

## Lean modules, in dependency order

1. `ZKGlobal/Epochs.lean` — finite protocol states, challenge schedule, fresh randomness, registered field variables and tag registry.
2. `ZKGlobal/ChallengeTree.lean` — fixed-tape deterministic causal prover, accepted challenge subsets, earliest-differing-bit special-soundness witness.
3. `ZKGlobal/ReplayProbability.lean` — exact joint-event probability $p(1-p+2^{-\kappa})^R$ and inequality $\le2^{-\kappa}+(R+1)^{-1}$.
4. `ZKGlobal/MainTranscript.lean` — checkpoint/restore semantics, perfect preservation of one main run and independence of the protected field challenges.
5. `ZKGlobal/CanonicalRegistry.lean` — stable tags, unique Pedersen bit openings except discrete-log collision, exact affine-to-parity extraction.
6. `ZKGlobal/OnlineExtraction.lean` — chronological finite-replay extractor, union bound $J(2^{-\kappa}+(R+1)^{-1})$, before-$\theta$/before-$z$ invariants.
7. `ZKGlobal/SoundnessReduction.lean` — false-claim event partition, algebraic error + external oracle error + discrete-log advantage + finite replay error, reduction complexity.
8. `ZKGlobal/Asymptotic.lean` — use replay budget $R=\lceil4J/\varepsilon\rceil$ to convert non-negligible false acceptance to non-negligible setup discrete-log advantage.
9. `ZKGlobal/Handoff.lean` — precise external authenticated KBFold oracle interface for Chapter 13.

## Main proved bound

```text
a := 2^(-kappa)
p := (# accepted challenge strings)/2^kappa
Pr[main block accepts AND all R side replays fail]
     = p * (1 - p + a)^R
     <= a + 1/(R+1)

Pr[main accepts AND some of J OR openings not extracted]
     <= J * (a + 1/(R+1))

Pr[false claim accepted]
     <= (ell+n)/2^n + eps_oracle + Adv_DL(D_R)
        + J * (a + 1/(R+1))
```

### Certified mathematical distinction

- The **main accepting execution is never replaced**. Replays use one saved classical prover state and its unchanged random tape; their transcripts are private to the reduction. The extracted values are therefore bound before the respective fresh outer challenge.
- Every proof **statement and commitment tag remains fixed** during its repeated mini-proofs. An inconsistent tag or parity aggregate yields an explicit setup discrete-log reduction.
- This is a classical **stand-alone public-coin knowledge-soundness reduction**, not a concurrent UC extractor, quantum rewinding argument or Fiat–Shamir/QROM theorem.
- The finite replay error can be made small relative to any *non-negligible cheating advantage* by a polynomial replay budget depending on a polynomial lower bound on that advantage. It is **not** automatically negligible for every fixed polynomial replay budget.
- External KBFold oracle and authenticated-opening consistency is *not* proved by this chapter. Its named error `eps_oracle` must be independently bounded in Chapter 13/14.
- The commitment and parity proof approach remains nonsuccinct and uses a classical discrete-logarithm assumption; it does not confer post-quantum security.

## Regression tests

`audit/global_extraction.rs` proves thousands of small combinatorial inequalities by exact integer arithmetic, exhaustively enumerates one-to-three-bit accepted challenge trees, and verifies the canonical collision-recovery formula in a deliberately insecure toy group. Rust CI only tests calculations, not formalizes the general theorem.

**Locked remaining blocks:** 13 — Complete Masked KBFold Protocol; 14 — Final Security Theorems; 15 — Certification and Audit. Do not create a Chapter 16.
