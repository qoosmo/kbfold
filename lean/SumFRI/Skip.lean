/-
SumFRI/Skip.lean
§5.3 of the Sum-FRI paper (committing to fewer words, Lemma 5.6) and Theorem 6.32 (committed
levels), item 1: soundness and evaluation binding transfer to `Π_eval^J` with the same errors.
The construction is that of `KBFold/Skip.lean` with the classical fold: the augmented prover
inserts the honest folds `cfold_{θ_j}(w_{j-1})` at the omitted levels.  `CommittedLevels` is
reused.  The transfer statements hold for every `J`.
-/
import SumFRI.Soundness
import KBFold.Skip

set_option autoImplicit false

open Polynomial Finset

namespace SumFRI

open KBFold

variable {F : Type*} [Field F]

namespace SumProver

variable {L : Subgroup Fˣ} {m : ℕ} (P : SumProver F L m)

/-- The augmented words of §5.3 (augmentation in Lemma 5.6).
`augW 0 = w₀`; a committed level is supplied by the prover, an omitted level is the honest local
fold of the preceding augmented word, and level `ℓ` is the verifier-computed word `ev(G)`. -/
noncomputable def augW (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (r : ℕ → F) :
    (j : ℕ) → (lv L j → F)
  | 0 => w0
  | k + 1 =>
      if k + 1 = ℓ then
        ev (lv L (k + 1)) (vpoly (P.g r))
      else if k + 1 ∈ J then
        P.orc (k + 1) r
      else
        cwfold (r k) (augW ℓ J w0 r k)

/-- The augmented prover from Lemma 5.6.  It has the same round polynomials
and final table as `P`.  For `j < ℓ` its oracle is `augW j`; for `j ≥ ℓ` we use the zero word,
which is ignored by the verifier (at `j = ℓ`, `W` is computed from `g`). -/
noncomputable def aug (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) : SumProver F L m where
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
        simp [SumProver.W, augW, aug]
      · have hlt : j + 1 < ℓ := by omega
        simp [SumProver.W, augW, aug, heq, hlt]

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

end SumProver

variable {L : Subgroup Fˣ} {m : ℕ}

/-- The verifier of `Π_eval^J` (§5.3).  It checks a fold only when the upper level is committed
(or is the final level `ℓ`).  At an omitted intermediate level the augmented word is, by
construction, the honest fold and no check is needed.

The left-hand side of the displayed check is the value that the paper's verifier obtains by
locally folding the opened coset of the committed word below (Lemma 5.5).  In this
word-level model the omitted intermediate words have already been inserted by `augW`, so the
same computation appears as one final `cwfold` step. -/
def SumProver.AcceptsJ (P : SumProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) {κ : ℕ}
    (zp : ℕ → F) (zs : Fin m → F) (v : F) (r : ℕ → F) (ξ : Fin κ → L) : Prop :=
  P.RestrOK ℓ zp v r ∧ P.ClosureOK ℓ zs v r ∧
    ∀ t,
      (∀ j < ℓ, (j + 1 ∈ J ∨ j + 1 = ℓ) →
        cwfold (r j) (P.augW ℓ J w0 r j) (ptAt (ξ t) (j + 1)) =
          P.augW ℓ J w0 r (j + 1) (ptAt (ξ t) (j + 1))) ∧
      (ℓ = 0 → w0 (ξ t) = (vpoly (P.g r)).eval (((ξ t : L) : Fˣ) : F))

/-- Acceptance probability of `Π_eval^J`, over the same challenge space as `sumAccProb`. -/
noncomputable def sumAccProbJ [Fintype F] [Fintype L] (P : SumProver F L m)
    (ℓ : ℕ) (J : Finset ℕ) (κ : ℕ) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F) : ℚ :=
  prob (fun ω : (Fin ℓ → F) × (Fin κ → L) =>
    P.AcceptsJ ℓ J w0 zp zs v (extR ω.1) ω.2)

/-- **Lemma 5.6 (skipping commitments).** Every accepting transcript of `Π_eval^J` becomes an
accepting transcript of `Π_eval` after insertion of the omitted honest folds. -/
theorem caccepts_aug (P : SumProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) {κ : ℕ}
    (zp : ℕ → F) (zs : Fin m → F) (v : F) (r : ℕ → F) (ξ : Fin κ → L) :
    P.AcceptsJ ℓ J w0 zp zs v r ξ → (P.aug ℓ J w0).Accepts ℓ w0 zp zs v r ξ := by
  rintro ⟨hSC, hCl, hQ⟩
  refine ⟨?_, ?_, fun t => ?_⟩
  · simpa [SumProver.RestrOK] using hSC
  · simpa [SumProver.ClosureOK] using hCl
  · refine ⟨?_, ?_⟩
    · intro j hj
      show cwfold (r j) ((P.aug ℓ J w0).W ℓ w0 r j) (ptAt (ξ t) (j + 1)) =
        (P.aug ℓ J w0).W ℓ w0 r (j + 1) (ptAt (ξ t) (j + 1))
      rw [P.aug_W_eq ℓ J w0 r j (by omega), P.aug_W_eq ℓ J w0 r (j + 1) (by omega)]
      by_cases hmark : j + 1 ∈ J ∨ j + 1 = ℓ
      · exact (hQ t).1 j hj hmark
      · have hne : j + 1 ≠ ℓ := fun e => hmark (Or.inr e)
        have hnot : j + 1 ∉ J := fun h => hmark (Or.inl h)
        simp [SumProver.augW, hne, hnot]
    · intro hzero
      simpa [SumProver.aug] using (hQ t).2 hzero

/-- Acceptance probability can only increase under augmentation (Lemma 5.6). -/
theorem csumAccProbJ_le [Fintype F] [Fintype L] (P : SumProver F L m)
    (ℓ : ℕ) (J : Finset ℕ) (κ : ℕ) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F) :
    sumAccProbJ P ℓ J κ w0 zp zs v ≤ sumAccProb (P.aug ℓ J w0) ℓ κ w0 zp zs v := by
  unfold sumAccProbJ sumAccProb
  apply prob_mono
  intro ω h
  exact caccepts_aug P ℓ J w0 zp zs v (extR ω.1) ω.2 h

/-- Augmentation preserves causality.  No hypothesis on `g` is needed: `aug.orc j` is zero for
`j ≥ ℓ`, while for `j < ℓ` the recursive `augW` never reaches its `g` branch. -/
theorem caug_causal (P : SumProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) :
    P.Causal → (P.aug ℓ J w0).Causal := by
  intro hC
  constructor
  · exact hC.1
  · intro j r r' h
    by_cases hj : j < ℓ
    · simp [SumProver.aug, hj, P.augW_congr ℓ J w0 hC j hj h]
    · simp [SumProver.aug, hj]

/-- Augmentation preserves the degree bound because the round polynomials are unchanged. -/
theorem caug_degOK (P : SumProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) :
    P.DegOK → (P.aug ℓ J w0).DegOK := by
  intro hdeg i r
  exact hdeg i r

/-- **Theorem 6.32, item 1 — far commitment.** Theorem 6.13(1) transfers to
`Π_eval^J` with exactly the same error. -/
theorem csoundness_far_J [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (P : SumProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (zp : ℕ → F)
    (zs : Fin m → F) (v : F) (δ : ℚ)
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (κ : ℕ)
    (hfar : ¬ FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ) :
    sumAccProbJ P ℓ J κ w0 zp zs v ≤ epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  calc
    sumAccProbJ P ℓ J κ w0 zp zs v
        ≤ sumAccProb (P.aug ℓ J w0) ℓ κ w0 zp zs v :=
      csumAccProbJ_le P ℓ J κ w0 zp zs v
    _ ≤ epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ :=
      csoundness_far (P := P.aug ℓ J w0) (ℓ := ℓ) (w0 := w0) (zp := zp) (zs := zs)
        (v := v) (δ := δ) hL hℓ hδ0 hδ (caug_causal P ℓ J w0 hC) κ hfar

/-- **Theorem 6.32, item 1 — wrong value.** Theorem 6.13(2) transfers to
`Π_eval^J` with exactly the same error. -/
theorem csoundness_close_J [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (P : SumProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (zp : ℕ → F)
    (zs : Fin m → F) (v : F) (δ : ℚ)
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hwrong : cpoly (cdecTable L (m + ℓ) δ w0) (catPt ℓ zp zs) ≠ v) :
    sumAccProbJ P ℓ J κ w0 zp zs v ≤
      epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F + (1 - δ) ^ κ := by
  calc
    sumAccProbJ P ℓ J κ w0 zp zs v
        ≤ sumAccProb (P.aug ℓ J w0) ℓ κ w0 zp zs v :=
      csumAccProbJ_le P ℓ J κ w0 zp zs v
    _ ≤ epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F + (1 - δ) ^ κ :=
      csoundness_close (P := P.aug ℓ J w0) (ℓ := ℓ) (w0 := w0) (zp := zp) (zs := zs)
        (v := v) (δ := δ) hL hℓ hδ0 hδ (caug_causal P ℓ J w0 hC)
        (caug_degOK P ℓ J w0 hdeg) κ hwrong

/-- **Theorem 6.32, item 1 — evaluation binding.** Corollary 6.14 transfers to
`Π_eval^J` with exactly the same error. -/
theorem ceval_binding_J [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (P : SumProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (zp : ℕ → F)
    (zs : Fin m → F) (v : F) (δ : ℚ)
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hacc : epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F + (1 - δ) ^ κ
      < sumAccProbJ P ℓ J κ w0 zp zs v) :
    FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ ∧
      v = cpoly (cdecTable L (m + ℓ) δ w0) (catPt ℓ zp zs) := by
  apply ceval_binding (P := P.aug ℓ J w0) (ℓ := ℓ) (w0 := w0) (zp := zp) (zs := zs)
    (v := v) (δ := δ) hL hℓ hδ0 hδ (caug_causal P ℓ J w0 hC)
    (caug_degOK P ℓ J w0 hdeg) κ
  exact hacc.trans_le (csumAccProbJ_le P ℓ J κ w0 zp zs v)

/-- **Theorem 6.32, item 1, for `Π_sum`:** Corollary 6.15 transfers to `Π_sum^J`. -/
theorem soundness_sum_J [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (P : SumProver F L m) (ℓ : ℕ) (J : Finset ℕ) (w0 : L → F) (v : F) (δ : ℚ)
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hwrong : ∑ a, cdecTable L (m + ℓ) δ w0 a ≠ v) :
    sumAccProbJ P ℓ J κ w0 (fun _ => 1) (fun _ => 1) v ≤
      epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F + (1 - δ) ^ κ := by
  refine csoundness_close_J P ℓ J w0 _ _ v δ hL hℓ hδ0 hδ hC hdeg κ ?_
  rw [catPt_one, cpoly_one]
  exact hwrong

end SumFRI
