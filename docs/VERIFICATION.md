# Verification report — "The Boolean-Kernel Basis" (version of 23 September 2026, with CDHZ and Lean)

## 1. Process

The paper was rewritten section by section, and the author validated each section before moving to the next.

Each rewritten section was then checked by an independent reviewer agent that had not written the text. The reviewer:
- re-derived every proof;
- checked edge cases;
- brute-forced identities in Python over F_17 and F_97, reaching 0 failures;
- re-checked the numeric claims.

A second independent reviewer audited the whole paper twice, for self-containedness, notation and claims. Every reported problem was fixed.

Code checks:
- `cargo test`: 15 tests pass, including two new tests in `tests/field_facts.rs`. They check the factorisation of p − 1 and that 7 generates F_p^*.
- `paper_checks`: 76 PASS, 0 FAIL.

## 2. Numbered items and status

Legend for the Checks column:
- **H** = proof checked by hand (author and reviewer)
- **N** = numerical check
- **C** = checked against the source

| Section | Items | Checks | Status |
|---|---|---|---|
| §2 Preliminaries | Lem 2.1, Fact 2.2 (LN97), Lem 2.3, Def 2.4, Lem 2.5, Prop 2.6, Cor 2.7, Def 2.8, Lem 2.9, Def 2.10, Lem 2.11, Lem 2.12, Def 2.14, Lem 2.15, Def 2.16–2.17, Lem 2.18–2.19, Fact 2.20 (WB86, Gao03), Lem 2.21 (Galois descent), Lem 2.22, Thm 2.23 (BCIKS Thm 4.1) | H, N; C for Thm 2.23 | correct |
| §3 Proof systems | Def 3.1, Lem 3.2–3.4, Def 3.5–3.7, Lem 3.8 (rbr ⇒ overall), Lem 3.9 (sumcheck), Def 3.10–3.11, Lem 3.12 (rbr-knowledge ⇒ binding), Lem 3.13 (Merkle binding) | H | correct |
| §3 Proof systems | Defs 3.14–3.15 (relaxed RBR knowledge, committed relations), Thm 3.16 (CDHZ Thms 6.10, 8.3, 11.3, specialised) | C (against the text of ePrint 2025/2166, version of 2 March 2026), re-derived by an independent reviewer | quoted theorem; derivation of the concrete bound checked |
| §4 Kernel basis | Def 4.1, Lem 4.3, Cor 4.4, Lem 4.5, Def 4.6, Lem 4.7, Thm 4.8, Rem 4.9, Def 4.10, Cor 4.11, Lem 4.12, Thm 4.13, Cor 4.14, Prop 4.15 | H, N (n = 0..6; det for n = 0..4) | correct |
| §5 Fold dictionary | Prop 5.1, Def 5.2, Thm 5.3, Cor 5.4, Def 5.5, Lem 5.6–5.7, Prop 5.8, Cor 5.9, Def 5.10, Prop 5.11, Ex 5.13 | H, N (F_97, n = 1..4) | correct |
| §6 PCS | Def 6.1, Lem 6.2, Lem 6.4 (honest prover), Thm 6.5 (completeness, all ℓ ∈ ⟦0,n⟧) | H, N | correct |
| §7 Soundness | Def 7.1, Lem 7.2–7.3, Def 7.4, Lem 7.6–7.7, Def 7.8, Lem 7.9–7.12, Thm 7.13, Cor 7.14, Prop 7.15 | H, N (lemmas 7.3, 7.9 and 7.10 brute-forced over F_17, 2,371 cases, 0 violations) | correct |
| §7 Soundness | Def 7.16, Lem 7.17–7.18, Thm 7.19, Prop 7.21 (round-by-round knowledge soundness) | H; checked condition by condition against Def 3.7 | correct |
| §7 Soundness | §7.7: Lem 7.22 (sampling), Def 7.23, Lem 7.24 (erasures), Thm 7.25 (relaxed RBR knowledge), Cor 7.26 (post-quantum), Lem 7.27 (uniqueness of committed witnesses) | H; two rounds of independent review against CDHZ; Lean (`NonInteractive`) | correct; Cor 7.26 relies on the quoted Thm 3.16 |
| §7 Soundness | Rem 7.28–7.29 (parameters) | N (`checks/pq_params.py` and `rust/examples/pq_params.rs`, exact rational arithmetic) | correct |

The parameter values checked in Remarks 7.28–7.29:
- post-quantum: κ = 248 queries give (5/8)^248 = 2^−168.16; with Q = 2^64, λ_H = 256, β = 320, the quartic extension (p⁴ > 2^255.99) and M ≤ 2^32, the bound of Thm 3.16 is ε_ext < 2^−31.84 (first term 2^−31.84, all other terms < 2^−51);
- classical: 148 queries give 2^−100.35; the quadratic extension has size p² > 2^127.9;
- ι⁴ − 7 is irreducible, by LN97 Theorem 3.75 (7 is a non-square mod p, p ≡ 1 mod 4); the reviewer also checked x^{p²} ≡ −x mod x⁴ − 7 numerically.

## 3. Corrections made in this version

1. **Assumption 3.15 removed.** The non-interactive layer now rests on published theorems:
   - Chiesa, Di, Hu and Zheng, ePrint 2025/2166 (Theorems 6.10, 8.3, 11.3): BCS for interactive oracle reductions in the QROM, with commitments chosen by the adversary and straightline extraction.
   - The definitions used (relations with implicit instance, R≤δ, relaxed RBR knowledge soundness, committed relations) are restated in §3.5, and the concrete bound is derived term by term (Thm 3.16).
   - New §7.7 proves that Π_eval, written as an IOR over Σ = F² (fibre strings), is relaxed RBR knowledge sound (Thm 7.25). This includes statements and messages with undefined entries (⊥), which the CDHZ extractor produces (found by the independent reviewer; fixed by erasure-aware witness sets, Lemma 7.24).
   - Post-quantum parameters recomputed with the explicit constants: κ = 248 (was 236), λ_H = 256.
2. **Non-negative round errors** made explicit in Defs 3.6–3.7 (Lemma 3.8 is false without it; found by the Lean formalisation).
3. **Notation.** Error terms renamed ε (κ is the number of queries); Merkle vector renamed 𝐝; Lemma 2.21 used an undefined σ (now Frob).
4. **Lean appendix** (Appendix B) with the correspondence table.

Earlier corrections (previous rewrite): vacuous knowledge relation replaced; "same affine line" corrected (Prop 5.11); binding across two proofs no longer claimed; missing lemmas added; n = 0 and ℓ = 0 cases covered.

## 4. What is NOT guaranteed

1. **Theorem 3.16 is quoted, not reproved.** Its constants were transcribed from the text extraction of ePrint 2025/2166 (version of 2 March 2026). The reviewer checked their internal consistency (Theorem 8.4 with Lemmas 8.7–8.8, and the proof of Theorem 6.10) and found no lost square roots. **Confirm the constants against the PDF before submission.**
2. **Scope of Corollary 7.26.**
   - It covers the compiler of CDHZ Construction 11.7 (salted Merkle trees, their challenge derivation), for one opening per proof.
   - It does **not** cover the Rust implementation as it stands (unsalted domain-separated Merkle trees, BLAKE3 hash-chain transcript, quadratic extension).
3. **External results used as axioms:**
   - BCIKS Theorem 4.1 (the only Lean axiom);
   - LN97 Theorems 2.8 and 3.75;
   - efficient Reed–Solomon decoding (Welch–Berlekamp, Gao), used only for running times.
4. **Not formalised in Lean:** Thm 3.16, Cor 7.26, Merkle lemmas, Facts 2.2 and 2.20, Lemma 2.21, running times, §8–§9. In Lean, Thm 7.25 is stated per round over a stage model of transcripts rather than through a general IOR structure.
5. **Review.** All manual review was done by AI agents. The Lean kernel check covers the formalised statements; a human referee should still read §3.5 and §7.7.

## 5. Lean formalisation

- Project: `lean/` (Lake package `KBFold`) (Lean 4.23.0, Mathlib v4.23.0), 16 modules, about 7000 lines.
- Full clean build in dependency order: no errors, no warnings.
- `grep sorry|admit`: nothing. Only axiom: `bciks_unique` (Theorem 2.23).
- `#print axioms` (file `KBFold/Audit.lean`): `fold_dictionary`, `ofCoordsLin_bijective`, `lowDegree_iff`, `eval_ofCoords`, `codeword_fold`, `completeness`, `rrbr_final`, `cr_unique_core`, `sumcheck_sound_iop` use only propext, Classical.choice, Quot.sound; `soundness_far`, `soundness_close`, `eval_binding`, `rbr_knowledge`, `rrbr_round` additionally use `bciks_unique`.
- Correspondence table: Appendix B of the paper.

Findings of the formalisation (no false statement found):
- Lemma 3.8 needs ε_i ≥ 0 (fixed);
- Thm 7.13(2) does not need Δ^fib ≤ δ;
- Cor 4.14 does not need M ≥ 2^t;
- several hypotheses are implied by the parameters (odd characteristic, ℓ ≤ n + R, N_j ≤ M_j).
