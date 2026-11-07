# Chapter 9 — Zero-Knowledge Ring Switching: Lean 4 Certification Map

**Paper audit:** 51 numbered definitions/results in seven source subsections: 14 definitions and **37 complete mathematical proofs**. Every non-definition result has a proof environment. **None of the new Chapter 9 results is claimed Lean-certified.**

## Individual statements

| Source | Kind | Statement | LaTeX label | Suggested Lean declaration | Status |
|---|---|---|---|---|---|
| `09a-model-and-protocol.tex` | definition | Admissible single-opening instance | `def:zkrs:instance` | `ZKRS.instance` | type/model |
| `09a-model-and-protocol.tex` | definition | Pre-challenge hidden state | `def:zkrs:prestate` | `ZKRS.prestate` | type/model |
| `09a-model-and-protocol.tex` | definition | Post-challenge hidden state | `def:zkrs:poststate` | `ZKRS.poststate` | type/model |
| `09a-model-and-protocol.tex` | definition | Public-message schedule | `def:zkrs:public-core` | `ZKRS.public_core` | type/model |
| `09a-model-and-protocol.tex` | lemma | Perfect consistency of an honest correction | `lem:zkrs:honest-correction` | `ZKRS.honest_correction` | paper proof |
| `09a-model-and-protocol.tex` | lemma | All three checker equations hold for honest values | `lem:zkrs:honest-checker` | `ZKRS.honest_checker` | paper proof |
| `09a-model-and-protocol.tex` | lemma | Complete algebraic correctness of the masked interfaces | `lem:zkrs:honest-relations` | `ZKRS.honest_relations` | paper proof |
| `09b-perfect-core.tex` | lemma | Masked input pair is jointly uniform | `lem:zkrs:input-uniform` | `ZKRS.input_uniform` | paper proof |
| `09b-perfect-core.tex` | lemma | Conditional trace-zero uniformity | `lem:zkrs:U-conditional` | `ZKRS.U_conditional` | paper proof |
| `09b-perfect-core.tex` | lemma | The public final scalar is conditionally uniform | `lem:zkrs:A-conditional` | `ZKRS.A_conditional` | paper proof |
| `09b-perfect-core.tex` | definition | Causal ideal public-core simulator | `def:zkrs:core-sim` | `ZKRS.core_sim` | type/model |
| `09b-perfect-core.tex` | theorem | Perfect public-core zero knowledge for one opening | `thm:zkrs:perfect-core` | `ZKRS.perfect_core` | paper proof |
| `09b-perfect-core.tex` | corollary | Conditional product law for fixed challenges | `cor:zkrs:product` | `ZKRS.product` | paper proof |
| `09c-conditional-witnesses.tex` | lemma | Two solutions of a trace-zero equation | `lem:zkrs:AS-fiber` | `ZKRS.AS_fiber` | paper proof |
| `09c-conditional-witnesses.tex` | lemma | Uniform conditional mask preimages | `lem:zkrs:AS-condition` | `ZKRS.AS_condition` | paper proof |
| `09c-conditional-witnesses.tex` | lemma | Conditioned vector mask is a product of two-point fibers | `lem:zkrs:vector-fiber` | `ZKRS.vector_fiber` | paper proof |
| `09c-conditional-witnesses.tex` | lemma | Conditional reconstruction of the last scalar mask | `lem:zkrs:rho-reconstruct` | `ZKRS.rho_reconstruct` | paper proof |
| `09c-conditional-witnesses.tex` | proposition | Algebraic completion for a fixed witness and a public core | `prop:zkrs:completion` | `ZKRS.completion` | paper proof |
| `09c-conditional-witnesses.tex` | lemma | Revealing the hidden pad breaks the single-opening privacy | `lem:zkrs:pad-disclosure` | `ZKRS.pad_disclosure` | paper proof |
| `09c-conditional-witnesses.tex` | corollary | Revealing the transposed pad has the same effect | `cor:zkrs:c-disclosure` | `ZKRS.c_disclosure` | paper proof |
| `09d-affine-interface.tex` | definition | Complete ideal affine verification | `def:zkrs:affine-checks` | `ZKRS.affine_checks` | type/model |
| `09d-affine-interface.tex` | lemma | The claimed-value and incoming tests are affine | `lem:zkrs:claim-in-affine` | `ZKRS.claim_in_affine` | paper proof |
| `09d-affine-interface.tex` | lemma | The outgoing test is affine | `lem:zkrs:out-affine` | `ZKRS.out_affine` | paper proof |
| `09d-affine-interface.tex` | lemma | Both anchored equations are affine in hidden variables | `lem:zkrs:anchor-affine` | `ZKRS.anchor_affine` | paper proof |
| `09d-affine-interface.tex` | definition | Algebraic residuals at the second challenge | `def:zkrs:errors` | `ZKRS.errors` | type/model |
| `09d-affine-interface.tex` | lemma | Accepted affine equations imply a residual root | `lem:zkrs:root-condition` | `ZKRS.root_condition` | paper proof |
| `09d-affine-interface.tex` | theorem | Any nonzero residual is detected with probability at least $1-n/q$ | `thm:zkrs:residual-detection` | `ZKRS.residual_detection` | paper proof |
| `09d-affine-interface.tex` | corollary | No secret squaring check is needed for this algebraic soundness | `cor:zkrs:no-quadratic-secret-check` | `ZKRS.no_quadratic_secret_check` | paper proof |
| `09d-affine-interface.tex` | lemma | Public trace checks impose no secret multiplication | `lem:zkrs:public-traces` | `ZKRS.public_traces` | paper proof |
| `09e-soundness-and-reuse.tex` | lemma | False claim forces a partial-evaluation discrepancy | `lem:zkrs:false-error` | `ZKRS.false_error` | paper proof |
| `09e-soundness-and-reuse.tex` | lemma | Correct hidden transposition gives a nonzero outgoing polynomial | `lem:zkrs:correct-c` | `ZKRS.correct_c` | paper proof |
| `09e-soundness-and-reuse.tex` | lemma | Incorrect hidden transposition gives a degree-$\ell$ mismatch | `lem:zkrs:incorrect-c` | `ZKRS.incorrect_c` | paper proof |
| `09e-soundness-and-reuse.tex` | theorem | Ideal masked ring-switching false-claim soundness | `thm:zkrs:false-sound` | `ZKRS.false_sound` | paper proof |
| `09e-soundness-and-reuse.tex` | definition | Two-opening pad-reuse experiment | `def:zkrs:reuse-game` | `ZKRS.reuse_game` | type/model |
| `09e-soundness-and-reuse.tex` | lemma | Reusing a pad reveals the difference of partial evaluations | `lem:zkrs:reuse-difference` | `ZKRS.reuse_difference` | paper proof |
| `09e-soundness-and-reuse.tex` | theorem | Perfect two-opening leakage under pad reuse | `thm:zkrs:reuse-attack` | `ZKRS.reuse_attack` | paper proof |
| `09e-soundness-and-reuse.tex` | corollary | Fresh partial-evaluation pads are necessary for this implementation | `cor:zkrs:fresh-pads` | `ZKRS.fresh_pads` | paper proof |
| `09f-ideal-and-composition.tex` | definition | Opaque commitment-and-affine ideal functionality | `def:zkrs:ideal-func` | `ZKRS.ideal_func` | type/model |
| `09f-ideal-and-composition.tex` | lemma | Opaque tokens do not perturb the public-core law | `lem:zkrs:opaque-kernels` | `ZKRS.opaque_kernels` | paper proof |
| `09f-ideal-and-composition.tex` | definition | Complete ideal verifier view | `def:zkrs:ideal-view` | `ZKRS.ideal_view` | type/model |
| `09f-ideal-and-composition.tex` | theorem | Perfect complete-view ZK in the opaque ideal model | `thm:zkrs:ideal-full-zk` | `ZKRS.ideal_full_zk` | paper proof |
| `09f-ideal-and-composition.tex` | definition | Sequential external-interface simulation contract | `def:zkrs:realization` | `ZKRS.realization` | type/model |
| `09f-ideal-and-composition.tex` | theorem | Conditional real-world statistical ZK composition | `thm:zkrs:conditional-zk` | `ZKRS.conditional_zk` | paper proof |
| `09f-ideal-and-composition.tex` | definition | External algebraic-soundness failure | `def:zkrs:sound-failure` | `ZKRS.sound_failure` | type/model |
| `09f-ideal-and-composition.tex` | theorem | Conditional full implementation soundness | `thm:zkrs:conditional-sound` | `ZKRS.conditional_sound` | paper proof |
| `09g-efficiency-ledger.tex` | definition | Field-message accounting for the public core | `def:zkrs:count` | `ZKRS.count` | type/model |
| `09g-efficiency-ledger.tex` | lemma | Exact single-opening public-core message count | `lem:zkrs:count` | `ZKRS.count` | paper proof |
| `09g-efficiency-ledger.tex` | lemma | Naive affine-coefficient count | `lem:zkrs:H-count` | `ZKRS.H_count` | paper proof |
| `09g-efficiency-ledger.tex` | lemma | Exact private state field-element count | `lem:zkrs:hidden-count` | `ZKRS.hidden_count` | paper proof |
| `09g-efficiency-ledger.tex` | definition | Certification milestones | `def:zkrs:milestones` | `ZKRS.milestones` | type/model |
| `09g-efficiency-ledger.tex` | proposition | Binary-field folding is not directly interchangeable with KBFold's $\pm x$ fold | `prop:zkrs:cross-field` | `ZKRS.cross_field` | paper proof |

## Suggested dependency-ordered Lean modules

1. `ZKRS/IdealProtocol.lean` — typed admissible binary-witness evaluation, one-opening sampling, causal challenge schedule.
2. `ZKRS/ConditionalUniform.lean` — joint uniform input messages, trace-zero conditional law and uniform final scalar.
3. `ZKRS/PublicSimulator.lean` — causal finite distribution kernel, perfect public-core simulation, fixed-challenge product law.
4. `ZKRS/MaskFibers.lean` — Artin--Schreier two-preimage fibers, exact posterior of hidden mask vector, hidden-value completion.
5. `ZKRS/AffineChecker.lean` — all hidden affine constraints, trace checks and polynomial residual root bound.
6. `ZKRS/AlgebraicSoundness.lean` — false-claim soundness at most `(ell+n)/|L|` under fixed-before-challenge assumptions.
7. `ZKRS/MultiOpening.lean` — two-opening pad reuse and perfect distinguishing attack.
8. `ZKRS/IdealFunctionality.lean` — opaque private registry, public independent tokens, constant honest acceptance.
9. `ZKRS/IdealZK.lean` — exact complete-view privacy **only in opaque ideal model**.
10. `ZKRS/ConditionalComposition.lean` — sequential external-interface simulation contract and hybrid theorem.
11. `ZKRS/CostAndGaps.lean` — message count, naive affine coefficient count, original KBFold field mismatch.

## Formal security boundary (non-negotiable)

- Theorem `thm:zkrs:perfect-core` proves exact joint public-core simulation `(m,y',theta,U,z,A)` for an arbitrary **causal** verifier, one valid opening and fresh pads. It excludes commitment roots, proofs and authenticated openings.
- Theorem `thm:zkrs:ideal-full-zk` proves full-view ZK only when an **ideal opaque interface** outputs witness-independent tokens and no unmasked openings.
- Theorem `thm:zkrs:conditional-zk` is a conditional implication: **a concrete external scheme must actually prove its entire sequential simulation contract**, including correlations with the public core.
- Theorem `thm:zkrs:false-sound` requires `w,w_hat,p,c,m,y'` bound **before theta**, auxiliary checker values fixed **before z**, and ideal enforcement of all affine constraints. The implementation error is an additional term.
- Theorem `thm:zkrs:reuse-attack` shows that reusing a single partial-evaluation pad across two openings is perfectly distinguishable even for equal authorized evaluation values.
- No direct integration with the current odd-characteristic KBFold word-fold, PCS proximity theorem, or QROM security is asserted.

## Main checked-on-paper identities

```
m = s_star + p
c = Transpose(p)
y_prime = y + p_in
V_k = eta_k * D_c(theta) + SUM_v H[v,k](theta)*p_v
U_k = V_k + t_k^2 + t_k
sigma = rho^2
A = rho + SUM_k W_k(z)*t_k
joint public core | chosen verifier challenges:
    m ~ Unif(L^n)
    y_prime ~ Unif(L)
    U | m,y_prime,theta ~ Unif((ker Trace)^n)
    A | m,y_prime,theta,U,z ~ Unif(L)
e_k = U_k + V_k + t_k^2+t_k
delta = sigma+rho^2
accepted anchors => delta+SUM_k e_k*W_k(z)^2=0
Pr[nonzero residual passes] <= n/|L|
Pr[false committed evaluation accepted] <= (ell+n)/|L|
```

**References:** Diamond--Posen 2024/504; Diamond 2025/1015; Kochergin 2026/2754; Frigo--shelat 2026/2770; KBFold parent manuscript.
