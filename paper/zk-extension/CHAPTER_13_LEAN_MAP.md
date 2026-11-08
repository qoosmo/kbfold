# Chapter 13 — Complete Masked KBFold Protocol and Authenticated Oracles

**Paper audit:** 47 labeled statements (19 definitions, **28 complete paper proofs**), with no new Chapter 13 Lean declarations certified.

**Locked scope:** Chapter 13 implements the odd-characteristic KBFold prover/verifier and its authenticated oracle interface. Only Chapters 14 (end-to-end security theorems) and 15 (Lean/Rust certification and final audit) remain. See [ROADMAP_LOCK.md](ROADMAP_LOCK.md).

## Statement-level certification map

| Section | Kind | Title | LaTeX label | Suggested Lean declaration | Status |
|---|---|---|---|---|---|
| `13a-commitment-oracles.tex` | definition | Canonical field encoding | `def:full:field-encoding` | `ZKFull.field_encoding` | typed contract |
| `13a-commitment-oracles.tex` | definition | Hiding commitment to a field symbol | `def:full:symbol-commit` | `ZKFull.symbol_commit` | typed contract |
| `13a-commitment-oracles.tex` | lemma | Perfect uniformity of a committed field symbol | `lem:full:leaf-uniform` | `ZKFull.leaf_uniform` | paper proof |
| `13a-commitment-oracles.tex` | definition | Domain-separated Merkle trees | `def:full:merkle` | `ZKFull.merkle` | typed contract |
| `13a-commitment-oracles.tex` | lemma | Perfect privacy of the authenticated shell | `lem:full:merkle-shell` | `ZKFull.merkle_shell` | paper proof |
| `13a-commitment-oracles.tex` | definition | Authenticated commitment opening | `def:full:auth-commit` | `ZKFull.auth_commit` | typed contract |
| `13a-commitment-oracles.tex` | lemma | Merkle opening conflict implies a hash collision | `lem:full:merkle-binding` | `ZKFull.merkle_binding` | paper proof |
| `13b-hidden-sumcheck.tex` | definition | True sumcheck states | `def:full:true-sum` | `ZKFull.true_sum` | typed contract |
| `13b-hidden-sumcheck.tex` | lemma | Exact sumcheck transition | `lem:full:true-transition` | `ZKFull.true_transition` | paper proof |
| `13b-hidden-sumcheck.tex` | definition | Hidden-offset masked sumcheck | `def:full:masked-round` | `ZKFull.masked_round` | typed contract |
| `13b-hidden-sumcheck.tex` | lemma | Endpoint carry for the round mask | `lem:full:mask-endpoints` | `ZKFull.mask_endpoints` | paper proof |
| `13b-hidden-sumcheck.tex` | theorem | Exact masked sumcheck invariant | `thm:full:masked-sumcheck` | `ZKFull.masked_sumcheck` | paper proof |
| `13b-hidden-sumcheck.tex` | lemma | Public evaluation weight at the last round | `lem:full:final-chi` | `ZKFull.final_chi` | paper proof |
| `13b-hidden-sumcheck.tex` | corollary | Masked sumcheck to linear fold closure | `cor:full:masked-final-link` | `ZKFull.masked_final_link` | paper proof |
| `13b-hidden-sumcheck.tex` | lemma | Publicly revealing the masked round coefficients is unsafe | `lem:full:quadratic-leak` | `ZKFull.quadratic_leak` | paper proof |
| `13c-fold-authentication.tex` | definition | Honest masked fold-oracle chain | `def:full:masked-oracles` | `ZKFull.masked_oracles` | typed contract |
| `13c-fold-authentication.tex` | lemma | Exact degree and word-fold invariants | `lem:full:fold-invariants` | `ZKFull.fold_invariants` | paper proof |
| `13c-fold-authentication.tex` | definition | Confidential authenticated fold query | `def:full:fold-query` | `ZKFull.fold_query` | typed contract |
| `13c-fold-authentication.tex` | lemma | The query equation is independent of square-root choice | `lem:full:fold-query-choice` | `ZKFull.fold_query_choice` | paper proof |
| `13c-fold-authentication.tex` | lemma | Honest confidential fold queries pass | `lem:full:fold-query-complete` | `ZKFull.fold_query_complete` | paper proof |
| `13c-fold-authentication.tex` | definition | Confidential final closure | `def:full:final-close` | `ZKFull.final_close` | typed contract |
| `13c-fold-authentication.tex` | lemma | Honest final closure is valid | `lem:full:final-complete` | `ZKFull.final_complete` | paper proof |
| `13c-fold-authentication.tex` | lemma | Degree-certified final word is uniquely determined by two values | `lem:full:two-unique` | `ZKFull.two_unique` | paper proof |
| `13d-complete-protocol.tex` | definition | Explicit relation-proof interface | `def:full:proof-engine` | `ZKFull.proof_engine` | typed contract |
| `13d-complete-protocol.tex` | definition | Public commitment registry | `def:full:registry` | `ZKFull.registry` | typed contract |
| `13d-complete-protocol.tex` | definition | Complete preprocessing relation | `def:full:pre-relation` | `ZKFull.pre_relation` | typed contract |
| `13d-complete-protocol.tex` | definition | Round relations | `def:full:round-relations` | `ZKFull.round_relations` | typed contract |
| `13d-complete-protocol.tex` | definition | Full protocol $\Pi_{\rm KBFold}^{\rm hid}$ | `def:full:protocol` | `ZKFull.protocol` | typed contract |
| `13d-complete-protocol.tex` | lemma | All protocol relations are finite arithmetic circuits | `lem:full:circuits` | `ZKFull.circuits` | paper proof |
| `13d-complete-protocol.tex` | theorem | Perfect algebraic completeness of the full protocol | `thm:full:completeness` | `ZKFull.completeness` | paper proof |
| `13e-online-view.tex` | definition | Public authenticated shell transcript | `def:full:shell-view` | `ZKFull.shell_view` | typed contract |
| `13e-online-view.tex` | lemma | Hiding roots can be sampled without any witness | `lem:full:simulate-roots` | `ZKFull.simulate_roots` | paper proof |
| `13e-online-view.tex` | lemma | Authenticated shell replies are deterministic after root construction | `lem:full:path-determined` | `ZKFull.path_determined` | paper proof |
| `13e-online-view.tex` | theorem | Perfect online privacy of the public shell | `thm:full:shell-online` | `ZKFull.shell_online` | paper proof |
| `13e-online-view.tex` | lemma | Any group commitment is mathematically openable to any fixed bit | `lem:full:exist-opening` | `ZKFull.exist_opening` | paper proof |
| `13e-online-view.tex` | corollary | Simulated public trees admit algebraically consistent hidden interpretations | `cor:full:exist-witness` | `ZKFull.exist_witness` | paper proof |
| `13e-online-view.tex` | definition | Full-proof simulation contract | `def:full:zk-contract` | `ZKFull.zk_contract` | typed contract |
| `13e-online-view.tex` | theorem | Conditional complete online-view simulation | `thm:full:conditional-online` | `ZKFull.conditional_online` | paper proof |
| `13f-soundness-cost.tex` | definition | Nonsuccinct full-relation soundness events | `def:full:sound-events` | `ZKFull.sound_events` | typed contract |
| `13f-soundness-cost.tex` | lemma | Sound full-relation checks fix the original evaluation | `lem:full:fixed-eval` | `ZKFull.fixed_eval` | paper proof |
| `13f-soundness-cost.tex` | theorem | Conditional full-relation false-evaluation bound | `thm:full:sound-conditional` | `ZKFull.sound_conditional` | paper proof |
| `13f-soundness-cost.tex` | definition | Sparse KBFold proximity obligation | `def:full:proximity` | `ZKFull.proximity` | typed contract |
| `13f-soundness-cost.tex` | lemma | Exact total fold-word size | `lem:full:total-words` | `ZKFull.total_words` | paper proof |
| `13f-soundness-cost.tex` | lemma | Bit-commitment count for fold oracles | `lem:full:word-count` | `ZKFull.word_count` | paper proof |
| `13f-soundness-cost.tex` | lemma | Authenticated query-shell complexity | `lem:full:query-cost` | `ZKFull.query_cost` | paper proof |
| `13f-soundness-cost.tex` | proposition | Full-relation mode has linear committed-word overhead | `prop:full:not-succinct` | `ZKFull.not_succinct` | paper proof |
| `13f-soundness-cost.tex` | definition | Locked Chapter 14 security inputs | `def:full:handoff` | `ZKFull.handoff` | typed contract |

## Dependency-ordered Lean modules

1. `ZKFull/FieldSymbol.lean` — odd-characteristic finite-field canonical bit encoding, Pedersen bit commitment vectors and valid encoding predicate.
2. `ZKFull/HidingMerkle.lean` — independent uniform group leaves, domain-separated hash tree, canonical authenticated shell, collision-to-conflict reduction.
3. `ZKFull/MaskedSumcheck.lean` — exact unmasked KBFold two-factor Sumcheck, secret affine offset mask $H_j$, concealed $\mu_j$ coefficients, endpoint and challenge invariants, final $\chi_m$.
4. `ZKFull/FoldOracles.lean` — source high-degree masked polynomial, normalized folds and degree budgets, hidden local query and final two-point closure.
5. `ZKFull/RelationCircuit.lean` — specified pre-evaluation, pre-challenge and post-challenge circuit relations; public/hidden inputs and named commitment registry.
6. `ZKFull/Protocol.lean` — complete interactive prover/verifier state machines, root-before-query timing, evaluation-after-initial-root, all ZK relation checks, full view.
7. `ZKFull/Completeness.lean` — perfect completeness relative to a perfectly complete circuit-proof engine.
8. `ZKFull/PublicShellSimulator.lean` — exact witness-independent online shell simulation including adaptive public query selection and consistent repeated Merkle paths.
9. `ZKFull/OnlineComposition.lean` — conditional full-view ZK based on a precise *joint adaptive proof-transcript simulation contract* for the chosen relation engine.
10. `ZKFull/ConditionalFullSoundness.lean` — pre-evaluation extraction, Pedersen/hash binding, circuit-soundness error union bound.
11. `ZKFull/SparseProximity.lean` — **open** enlarged-budget adversarial proximity theorem for sparse queries: $D_j=2^{m-j}+\lceil B/2^j\rceil$.
12. `ZKFull/Cost.lean` — exact committed word sizes $M(2-2^{-m})$, group-element counts $bM(2-2^{-m})$, query shells.
13. `ZKFull/SecurityModels.lean` — **open** classical interactive/ROM/QROM distinctions and actual relation-engine instantiation (Chapter 14 only).

## Exact theorem boundary

**Proved algebraically:**

```text
Q_0 = U_f + X^N R
Q_{j+1} = pfold_{r_j}(Q_j)
deg(Q_j) < D_j
H_j(T) = b_{j-1}/2 + c_j(2T-1)
mu_j(T) = s_j(T) + H_j(T)
b_j = H_j(r_{j-1})
mu_j(0)+mu_j(1) = sigma_{j-1}+b_{j-1}
mu_j(r_{j-1}) = sigma_j+b_j
mu_m(r_{m-1}) = chi_m * coeff0(Q_m) + b_m
```

Every public Merkle leaf is a vector of perfectly hiding Pedersen bit commitments; the word's actual field symbol is never exposed. The full online distribution of all public shell messages (excluding the relation proof transcripts) has a witness-free simulator.

**Conditional cryptographic theorems:**

```text
FullView ZK error <= eps_proofZK
    ONLY IF: actual relation engine satisfies online sequential
             adaptive proof-transcript simulation contract.

False claim in full-relation mode:
    eps_snd <= eps_pre + eps_rel + eps_bind + eps_hash
    ONLY IF: pre-point witness knowledge, fixed registered
             commitments, relation soundness, Pedersen binding
             and collision resistance are established.

Sparse mode:
    needs new adversarial proximity argument eps_prox for D_j/M_j.
```

The *full-relation* reference protocol uses one relation circuit over the complete committed word and is **not succinct**; the original sparse KBFold PCS complexity is not carried over. The Pedersen bit commitments are classical and not post-quantum secure.

## Reproducible tests

`audit/full_kbfold.rs` extends the existing odd-field Rust folding audit to check hidden-offset masked Sumcheck rounds, final weight multiplication, linear closure, local hidden fold equations, and exact group uniformity in a deliberately insecure toy Pedersen group. The tests are executable algebraic checks, not a substitute for zero-knowledge or hash security proofs.
