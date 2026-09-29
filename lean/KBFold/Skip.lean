/-
KBFold/Skip.lean
§6.3 of the paper ("Committing to fewer words" / "Skipping commitments") and
§7.6, Theorem "Committed levels", item 1.

The public parameter `J` is represented by a `Finset ℕ`; the intended paper condition is
`CommittedLevels ℓ J`, i.e. `J ⊆ {0, …, ℓ-1}` and `0 ∈ J`.  The transfer statements below are
actually valid for every `J`, so they do not need this condition as a hypothesis.

The augmented prover exposes `augW` through `orc` only at indices `j < ℓ`.  At `j ≥ ℓ` its
`orc` is the zero word.  These values are ignored by `EvalProver.W` at the final level and by the
verifier thereafter; choosing zero avoids imposing a causality hypothesis on `g`, which the
existing `EvalProver.Causal` definition does not constrain.
-/
import KBFold.Soundness

set_option autoImplicit false

open Polynomial Finset

namespace KBFold

variable {F : Type*} [Field F]

/-- The valid committed-level sets of §6.3: `J ⊆ [0, ℓ-1]` and `0 ∈ J`. -/
def CommittedLevels (ℓ : ℕ) (J : Finset ℕ) : Prop :=
  0 ∈ J ∧ ∀ j ∈ J, j < ℓ

namespace EvalProver

variable {L : Subgroup Fˣ} {m : ℕ} (P : EvalProver F L m)

/-- The augmented words of §6.3 (augmentation in Lemma "Skipping commitments").
`augW 0 = w₀`; a committed level is supplied by the prover, an omitted level is the honest local
fold of the preceding augmented word, and level `ℓ` is the verifier-computed word `ev(G)`. -/
noncomputable def augW (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (r : ℕ → F) :
    (j : ℕ) → (lv L j → F)
  | 0 => w0
  | k + 1 =>
      if k + 1 = ℓ then
        ev (lv L (k + 1)) (ofCoords (P.g r))
      else if k + 1 ∈ J then
        P.orc (k + 1) r
      else
        wfold (r k) (augW ℓ J w0 r k)

/-- The augmented prover from Lemma "Skipping commitments".  It has the same round polynomials
and final table as `P`.  For `j < ℓ` its oracle is `augW j`; for `j ≥ ℓ` we use the zero word,
which is ignored by the verifier (at `j = ℓ`, `W` is computed from `g`). -/
noncomputable def aug (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) : EvalProver F L m where
  s := P.s
  orc := fun j r => if j < ℓ then P.augW ℓ J w0 r j else fun _ => 0
  g := P.g

@[simp] theorem aug_vv (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (v : F) (r : ℕ → F) :
    (P.aug ℓ J w0).vv v r = P.vv v r := by
  funext i
  cases i <;> rfl

/-- The verifier word sequence of the augmented prover is exactly `augW` through level `ℓ`. -/
theorem aug_W_eq (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (r : ℕ → F) :
    ∀ j, j ≤ ℓ → (P.aug ℓ J w0).W ℓ w0 r j = P.augW ℓ J w0 r j
  | 0, _ => rfl
  | j + 1, hj => by
      by_cases heq : j + 1 = ℓ
      · subst heq
        simp [EvalProver.W, augW, aug]
      · have hlt : j + 1 < ℓ := by omega
        simp [EvalProver.W, augW, aug, heq, hlt]

/-- `augW j` depends only on `r 0, …, r (j-1)` as long as `j < ℓ`.
The final branch `j = ℓ`, which reads `g`, is deliberately excluded because `Causal` does not
constrain `g`; `aug.orc` does not expose that branch. -/
theorem augW_congr (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (hC : P.Causal) {r r' : ℕ → F} :
    ∀ j, j < ℓ → (∀ k < j, r k = r' k) → P.augW ℓ J w0 r j = P.augW ℓ J w0 r' j
  | 0, _, _ => rfl
  | j + 1, hj, h => by
      have hne : j + 1 ≠ ℓ := by omega
      have ih : P.augW ℓ J w0 r j = P.augW ℓ J w0 r' j :=
        augW_congr ℓ J w0 hC j (by omega) (fun k hk => h k (by omega))
      by_cases hJ : j + 1 ∈ J
      · simp only [augW, hne, hJ, if_false, if_true]
        exact hC.2 (j + 1) r r' h
      · simp only [augW, hne, hJ, if_false]
        rw [h j (by omega), ih]

end EvalProver

variable {L : Subgroup Fˣ} {m : ℕ}

/-- The verifier of `Π_eval^J` (§6.3).  It checks a fold only when the upper level is committed
(or is the final level `ℓ`).  At an omitted intermediate level the augmented word is, by
construction, the honest fold and no check is needed.

The left-hand side of the displayed check is the value that the paper's verifier obtains by
locally folding the opened coset of the committed word below (Lemma "Local folding").  In this
word-level model the omitted intermediate words have already been inserted by `augW`, so the
same computation appears as one final `wfold` step. -/
def EvalProver.AcceptsJ (P : EvalProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) {κ : ℕ}
    (zp : ℕ → F) (zs : Fin m → F) (v : F) (r : ℕ → F) (ξ : Fin κ → L) : Prop :=
  P.SumcheckOK ℓ v r ∧ P.ClosureOK ℓ zp zs v r ∧
    ∀ t,
      (∀ j < ℓ, (j + 1 ∈ J ∨ j + 1 = ℓ) →
        wfold (r j) (P.augW ℓ J w0 r j) (ptAt (ξ t) (j + 1)) =
          P.augW ℓ J w0 r (j + 1) (ptAt (ξ t) (j + 1))) ∧
      (ℓ = 0 → w0 (ξ t) = (ofCoords (P.g r)).eval (((ξ t : L) : Fˣ) : F))

/-- Acceptance probability of `Π_eval^J`, over the same challenge space as `evalAccProb`. -/
noncomputable def evalAccProbJ [Fintype F] [Fintype L] (P : EvalProver F L m)
    (ℓ : ℕ) (J : Finset ℕ) (κ : ℕ) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F) : ℚ :=
  prob (fun ω : (Fin ℓ → F) × (Fin κ → L) =>
    P.AcceptsJ ℓ J w0 zp zs v (extR ω.1) ω.2)

/-- **Lemma (Skipping commitments), §6.3.** Every accepting transcript of `Π_eval^J` becomes an
accepting transcript of `Π_eval` after insertion of the omitted honest folds. -/
theorem accepts_aug (P : EvalProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) {κ : ℕ}
    (zp : ℕ → F) (zs : Fin m → F) (v : F) (r : ℕ → F) (ξ : Fin κ → L) :
    P.AcceptsJ ℓ J w0 zp zs v r ξ → (P.aug ℓ J w0).Accepts ℓ w0 zp zs v r ξ := by
  rintro ⟨hSC, hCl, hQ⟩
  refine ⟨?_, ?_, fun t => ?_⟩
  · simpa [EvalProver.SumcheckOK] using hSC
  · simpa [EvalProver.ClosureOK] using hCl
  · refine ⟨?_, ?_⟩
    · intro j hj
      show wfold (r j) ((P.aug ℓ J w0).W ℓ w0 r j) (ptAt (ξ t) (j + 1)) =
        (P.aug ℓ J w0).W ℓ w0 r (j + 1) (ptAt (ξ t) (j + 1))
      rw [P.aug_W_eq ℓ J w0 r j (by omega), P.aug_W_eq ℓ J w0 r (j + 1) (by omega)]
      by_cases hmark : j + 1 ∈ J ∨ j + 1 = ℓ
      · exact (hQ t).1 j hj hmark
      · have hne : j + 1 ≠ ℓ := fun e => hmark (Or.inr e)
        have hnot : j + 1 ∉ J := fun h => hmark (Or.inl h)
        simp [EvalProver.augW, hne, hnot]
    · intro hzero
      simpa [EvalProver.aug] using (hQ t).2 hzero

/-- Acceptance probability can only increase under augmentation (Lemma "Skipping commitments"). -/
theorem accProbJ_le [Fintype F] [Fintype L] (P : EvalProver F L m)
    (ℓ : ℕ) (J : Finset ℕ) (κ : ℕ) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F) :
    evalAccProbJ P ℓ J κ w0 zp zs v ≤ evalAccProb (P.aug ℓ J w0) ℓ κ w0 zp zs v := by
  unfold evalAccProbJ evalAccProb
  apply prob_mono
  intro ω h
  exact accepts_aug P ℓ J w0 zp zs v (extR ω.1) ω.2 h

/-- Augmentation preserves causality.  No hypothesis on `g` is needed: `aug.orc j` is zero for
`j ≥ ℓ`, while for `j < ℓ` the recursive `augW` never reaches its `g` branch. -/
theorem aug_causal (P : EvalProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) :
    P.Causal → (P.aug ℓ J w0).Causal := by
  intro hC
  constructor
  · exact hC.1
  · intro j r r' h
    by_cases hj : j < ℓ
    · simp [EvalProver.aug, hj, P.augW_congr ℓ J w0 hC j hj h]
    · simp [EvalProver.aug, hj]

/-- Augmentation preserves the degree bound because the round polynomials are unchanged. -/
theorem aug_degOK (P : EvalProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) :
    P.DegOK → (P.aug ℓ J w0).DegOK := by
  intro hdeg i r
  exact hdeg i r

/-- **Theorem (Committed levels), item 1 — far commitment.** Theorem 7.13(1) transfers to
`Π_eval^J` with exactly the same error. -/
theorem soundness_far_J [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (P : EvalProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (zp : ℕ → F)
    (zs : Fin m → F) (v : F) (δ : ℚ)
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (κ : ℕ)
    (hfar : ¬ FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ) :
    evalAccProbJ P ℓ J κ w0 zp zs v ≤ epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  calc
    evalAccProbJ P ℓ J κ w0 zp zs v
        ≤ evalAccProb (P.aug ℓ J w0) ℓ κ w0 zp zs v :=
      accProbJ_le P ℓ J κ w0 zp zs v
    _ ≤ epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ :=
      soundness_far (P := P.aug ℓ J w0) (ℓ := ℓ) (w0 := w0) (zp := zp) (zs := zs)
        (v := v) (δ := δ) hL hℓ hδ0 hδ (aug_causal P ℓ J w0 hC) κ hfar

/-- **Theorem (Committed levels), item 1 — wrong value.** Theorem 7.13(2) transfers to
`Π_eval^J` with exactly the same error. -/
theorem soundness_close_J [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (P : EvalProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (zp : ℕ → F)
    (zs : Fin m → F) (v : F) (δ : ℚ)
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hwrong : mle (decTable L (m + ℓ) δ w0) (catPt ℓ zp zs) ≠ v) :
    evalAccProbJ P ℓ J κ w0 zp zs v ≤
      epsFold F (m + ℓ + R) ℓ + 2 * ℓ / Fintype.card F + (1 - δ) ^ κ := by
  calc
    evalAccProbJ P ℓ J κ w0 zp zs v
        ≤ evalAccProb (P.aug ℓ J w0) ℓ κ w0 zp zs v :=
      accProbJ_le P ℓ J κ w0 zp zs v
    _ ≤ epsFold F (m + ℓ + R) ℓ + 2 * ℓ / Fintype.card F + (1 - δ) ^ κ :=
      soundness_close (P := P.aug ℓ J w0) (ℓ := ℓ) (w0 := w0) (zp := zp) (zs := zs)
        (v := v) (δ := δ) hL hℓ hδ0 hδ (aug_causal P ℓ J w0 hC)
        (aug_degOK P ℓ J w0 hdeg) κ hwrong

/-- **Theorem (Committed levels), item 1 — evaluation binding.** Corollary 7.14 transfers to
`Π_eval^J` with exactly the same error. -/
theorem eval_binding_J [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (P : EvalProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (zp : ℕ → F)
    (zs : Fin m → F) (v : F) (δ : ℚ)
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hacc : epsFold F (m + ℓ + R) ℓ + 2 * ℓ / Fintype.card F + (1 - δ) ^ κ
      < evalAccProbJ P ℓ J κ w0 zp zs v) :
    FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ ∧
      v = mle (decTable L (m + ℓ) δ w0) (catPt ℓ zp zs) := by
  apply eval_binding (P := P.aug ℓ J w0) (ℓ := ℓ) (w0 := w0) (zp := zp) (zs := zs)
    (v := v) (δ := δ) hL hℓ hδ0 hδ (aug_causal P ℓ J w0 hC)
    (aug_degOK P ℓ J w0 hdeg) κ
  exact hacc.trans_le (accProbJ_le P ℓ J κ w0 zp zs v)

end KBFold
