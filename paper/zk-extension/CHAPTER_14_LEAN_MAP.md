# Chapter 14 — Final Security Theorems (Lean 4 map)

**Paper audit:** 43 labeled definitions/results, with **28 complete manuscript proofs** and 15 definitions. None of the Chapter 14 declarations has been machine certified yet.

**Locked manuscript:** Chapter 15 is the final block. There is no Chapter 16. See [ROADMAP_LOCK.md](ROADMAP_LOCK.md).

## Statement-by-statement certification map

| Source | Kind | Title | LaTeX label | Suggested Lean declaration | Status |
|---|---|---|---|---|---|
| `14a-security-games.tex` | definition | Classical commitment setup | `def:security14:setup` | `ZKFinal.setup` | model / contract |
| `14a-security-games.tex` | definition | One-opening evaluation-binding game | `def:security14:binding-game` | `ZKFinal.binding_game` | model / contract |
| `14a-security-games.tex` | definition | Authorized one-opening zero-knowledge game | `def:security14:zk-game` | `ZKFinal.zk_game` | model / contract |
| `14a-security-games.tex` | definition | Online relation-engine extraction contract | `def:security14:extract-contract` | `ZKFinal.extract_contract` | model / contract |
| `14a-security-games.tex` | definition | Adaptive witness-indistinguishability contract | `def:security14:wi-contract` | `ZKFinal.wi_contract` | model / contract |
| `14a-security-games.tex` | definition | Reduction error terms | `def:security14:errors` | `ZKFinal.errors` | model / contract |
| `14a-security-games.tex` | lemma | Completeness carries to the final security game | `lem:security14:complete` | `ZKFinal.complete` | paper proof |
| `14b-full-soundness.tex` | lemma | Canonical bit opening is unique except under discrete-log failure | `lem:security14:canonical` | `ZKFinal.canonical` | paper proof |
| `14b-full-soundness.tex` | lemma | A changed authenticated leaf gives a hash collision | `lem:security14:same-root` | `ZKFinal.same_root` | paper proof |
| `14b-full-soundness.tex` | lemma | The preprocessing witness fixes one source table | `lem:security14:pre-fixed` | `ZKFinal.pre_fixed` | paper proof |
| `14b-full-soundness.tex` | theorem | End-to-end classical evaluation binding: full-relation mode | `thm:security14:full-binding` | `ZKFinal.full_binding` | paper proof |
| `14b-full-soundness.tex` | corollary | Knowledge-soundness of the expanded witness relation | `cor:security14:knowledge` | `ZKFinal.knowledge` | paper proof |
| `14b-full-soundness.tex` | proposition | Random challenges are unnecessary for full-relation algebraic binding | `prop:security14:uniform-not-needed` | `ZKFinal.uniform_not_needed` | paper proof |
| `14c-equivocal-online-zk.tex` | definition | Simulated commitment key | `def:security14:sim-key` | `ZKFinal.sim_key` | model / contract |
| `14c-equivocal-online-zk.tex` | lemma | Simulated and real commitment keys have identical public laws | `lem:security14:sim-key-law` | `ZKFinal.sim_key_law` | paper proof |
| `14c-equivocal-online-zk.tex` | definition | Trapdoor equivocation algorithm | `def:security14:equiv` | `ZKFinal.equiv` | model / contract |
| `14c-equivocal-online-zk.tex` | theorem | Exact trapdoor equivocation with uniform public commitments | `thm:security14:equiv-perfect` | `ZKFinal.equiv_perfect` | paper proof |
| `14c-equivocal-online-zk.tex` | definition | Online equivocal full-protocol simulator | `def:security14:online-sim` | `ZKFinal.online_sim` | model / contract |
| `14c-equivocal-online-zk.tex` | lemma | The virtual source matches every authorized one-point claim | `lem:security14:virtual-eval` | `ZKFinal.virtual_eval` | paper proof |
| `14c-equivocal-online-zk.tex` | lemma | Every simulated circuit statement has a known valid witness | `lem:security14:sim-witnesses` | `ZKFinal.sim_witnesses` | paper proof |
| `14c-equivocal-online-zk.tex` | lemma | The simulator's public authenticated shells have the honest law | `lem:security14:eq-shell-law` | `ZKFinal.eq_shell_law` | paper proof |
| `14c-equivocal-online-zk.tex` | theorem | Constructive classical online zero knowledge: full-relation mode | `thm:security14:online-zk` | `ZKFinal.online_zk` | paper proof |
| `14c-equivocal-online-zk.tex` | corollary | Perfect zero knowledge under perfect adaptive WI | `cor:security14:perfect-wi` | `ZKFinal.perfect_wi` | paper proof |
| `14d-sparse-proximity.tex` | definition | Enlarged masked Reed--Solomon codes | `def:security14:codes` | `ZKFinal.codes` | model / contract |
| `14d-sparse-proximity.tex` | lemma | Exact dimension and minimum distance | `lem:security14:rs-distance` | `ZKFinal.rs_distance` | paper proof |
| `14d-sparse-proximity.tex` | lemma | Degree-rate bounds and required blow-up | `lem:security14:rates` | `ZKFinal.rates` | paper proof |
| `14d-sparse-proximity.tex` | lemma | Folding a monomial halves its exponent | `lem:security14:half-exp` | `ZKFinal.half_exp` | paper proof |
| `14d-sparse-proximity.tex` | theorem | Sparse local folds and final linearity do not certify initial degree | `thm:security14:sparse-counterexample` | `ZKFinal.sparse_counterexample` | paper proof |
| `14d-sparse-proximity.tex` | lemma | Exact fixed-discrepancy sampling error | `lem:security14:query-detection` | `ZKFinal.query_detection` | paper proof |
| `14d-sparse-proximity.tex` | definition | Actual sparse proximity contract | `def:security14:proximity-contract` | `ZKFinal.proximity_contract` | model / contract |
| `14d-sparse-proximity.tex` | proposition | A fixed discrepancy bound is not a proximity theorem | `prop:security14:not-proximity` | `ZKFinal.not_proximity` | paper proof |
| `14d-sparse-proximity.tex` | theorem | Conditional sparse soundness composition | `thm:security14:sparse-sound` | `ZKFinal.sparse_sound` | paper proof |
| `14e-classical-rom-quantum.tex` | definition | Four distinct claims | `def:security14:models` | `ZKFinal.models` | model / contract |
| `14e-classical-rom-quantum.tex` | lemma | A known Pedersen setup logarithm gives two openings | `lem:security14:known-alpha` | `ZKFinal.known_alpha` | paper proof |
| `14e-classical-rom-quantum.tex` | theorem | Quantum break of classical Pedersen-based binding | `thm:security14:quantum-break` | `ZKFinal.quantum_break` | paper proof |
| `14e-classical-rom-quantum.tex` | corollary | No post-quantum theorem for the present Pedersen instantiation | `cor:security14:no-pq` | `ZKFinal.no_pq` | paper proof |
| `14e-classical-rom-quantum.tex` | proposition | Original KBFold QROM soundness does not automatically transfer | `prop:security14:qrom-nontransfer` | `ZKFinal.qrom_nontransfer` | paper proof |
| `14e-classical-rom-quantum.tex` | definition | Required post-quantum replacement contract | `def:security14:pq-replacement` | `ZKFinal.pq_replacement` | model / contract |
| `14f-final-ledger.tex` | definition | Classical reference-protocol assumption package | `def:security14:package` | `ZKFinal.package` | model / contract |
| `14f-final-ledger.tex` | theorem | Final classical reference-protocol theorem | `thm:security14:final` | `ZKFinal.final` | paper proof |
| `14f-final-ledger.tex` | corollary | Asymptotic conditional classical security | `cor:security14:negligible` | `ZKFinal.negligible` | paper proof |
| `14f-final-ledger.tex` | definition | Outstanding proof ledger for Chapter 15 | `def:security14:open` | `ZKFinal.open` | model / contract |
| `14f-final-ledger.tex` | proposition | The four-block scope is closed | `prop:security14:locked` | `ZKFinal.locked` | paper proof |

## Dependency order and formalization obligations

1. `ZKFinal/SecurityGames.lean`: one-point evaluation binding, honest pre-evaluation source extraction, causal verifier view, distinct classical/ROM/QROM adversary types.
2. `ZKFinal/PedersenBinding.lean`: bitwise conflicting openings reveal setup exponent; same bit gives unique blinding.
3. `ZKFinal/MerkleBinding.lean`: conflicting authentication shells under one root yield a hash collision.
4. `ZKFinal/FullRelationSoundness.lean`: exact claimed-evaluation circuit relation implies binding outside explicit extraction, DL, and hash bad events.
5. `ZKFinal/TrapdoorEquivocation.lean`: generator $h=g^\alpha$; exact setup distribution; $C=h^\rho$ can open to bit $b$ with $r_b=\rho-b/\alpha$; uniformity.
6. `ZKFinal/VirtualEvaluation.lean`: constant virtual source table $f^z\equiv v$ has multilinear evaluation $v$ at every point.
7. `ZKFinal/OnlineSimulator.lean`: simulation-specific pre-source $f^{pre}=0$, post-point virtual source $f^z=v$; exact public-shell law, and conditional computational ZK under *adaptive multi-proof witness indistinguishability* of the chosen NP proof engine. No instantiated proof-engine certification is claimed.
8. `ZKFinal/RSRates.lean`: exact enlarged degree budgets, dimensions and minimum distances.
9. `ZKFinal/SparseCounterexample.lean`: for $1\le B<N$, $X^{N+B}$ is not in $RS(\Omega_0,N+B)$ yet all normalized local fold relations hold and the final word is linear for every challenge vector. This does NOT violate the fully checked source-binding circuit.
10. `ZKFinal/FixedDiscrepancy.lean`: exact independent sampling error $(1-e/M_j)^q$, explicitly **not** a code proximity theorem.
11. `ZKFinal/QuantumBreak.lean`: knowledge of $\alpha$ permits equivocation; a quantum algorithm for discrete logarithms breaks binding, making a false-claim strategy possible even with perfectly complete circuit proofs. Formal quantum algorithm statement is an external premise (Shor).
12. `ZKFinal/FinalComposition.lean`: conditional classical completeness, soundness and online ZK; exact error budgets and uninstantiated assumptions.

## Final achieved results vs unproved cryptographic assumptions

### Paper proofs

```text
Full-relation classical false-evaluation:
  eps_sound <= eps_KE + eps_DL + eps_CRH

Classical online ZK in a simulatable CRS:
  Adv_ZK <= eps_WI

Pedersen simulation trapdoor:
  h = g^alpha ; C = h^rho ; r_b = rho - b/alpha
  g^b * h^(r_b) = C

Enlarged RS rate:
  D_j/M_j = 2^(-s) * (1 + ceil(B/2^j)/N_j)

Sparse obstruction:
  1 <= B < N ; deg(X^(N+B)) = D_0
  X^(N+B) not in RS(Omega_0,D_0)
  m normalized folds -> degree <= 1
```

### Not proved / must not be advertised as solved

- **Concrete odd-field NP proof engine:** prefix-preserving extraction for all pre-commitment and adaptive relation proofs; adaptive multi-proof WI for arbitrary classical malicious verifiers. A fully specified circuit relation is **not** an instantiated cryptographic argument of knowledge.
- **Succinct sparse proximity:** combined initial source/degree binding and adversarial proximity for the **enlarged** $D_j$ budgets.
- **Quantum security:** the current standard Pedersen groups are explicitly broken by quantum discrete-log algorithms; cannot inherit original KBFold QROM soundness.
- **Fiat--Shamir ROM:** needs a separate reduction for this altered transcript and proof engine.
- **Formal certification:** new Chapter 14 results are mathematical manuscript proofs, not Lean checked.

## Rust tests

`audit/final_security.rs`: exact trapdoor-equivocation algebra for all small test keys; the non-codeword polynomial $X^{N+B}$ passing every local fold and final line across F_97 domains; enlarged Reed--Solomon rate/distance inequalities. This is regression validation, not cryptographic proof or a quantum experiment.

## Last block

**Chapter 15 — Lean/Rust certification, complexity and final manuscript audit only.** Complete artifacts and proof ledger, identify unproved assumptions, and do not expand the chapter structure.
