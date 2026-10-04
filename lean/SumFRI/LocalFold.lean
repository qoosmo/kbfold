/-
SumFRI/LocalFold.lean
* Lemma 4.8(3) (explicit formula of the classical word fold) `cwfold_sqPt`;
* Lemma 5.5 (local folding) `cfoldUp_local`: `d` successive classical folds of a word `w` on a
  domain `D`, at the point `ξ^{2^d}`, depend only on the values of `w` on the coset
  `S(ξ) = {ζ ∈ D : ζ^{2^d} = ξ^{2^d}}`.  (The operation count `2^d - 1` of the paper is not
  formalised.)
-/
import SumFRI.Fibre

set_option autoImplicit false

namespace SumFRI

open KBFold

variable {F : Type*} [Field F]

/-- **Lemma 4.8(3) (explicit formula):**
`cfold_θ(w)(ξ²) = ((ξ + θ) w(ξ) + (ξ - θ) w(-ξ)) / (2ξ)`. -/
theorem cwfold_sqPt {L : Subgroup Fˣ} (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (θ : F)
    (w : L → F) (ξ : L) :
    cwfold θ w (sqPt ξ) = ((xv ξ + θ) * w ξ + (xv ξ - θ) * w (negPt ξ)) / (2 * xv ξ) := by
  simp only [cwfold, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [evenW_sqPt hL, oddW_sqPt hL]
  have hξ : xv ξ ≠ 0 := Units.ne_zero _
  field_simp
  ring

/-- **Lemma 5.5 (local folding).** For a word `w` on `D` and `ξ ∈ D`, the value of the `d`-fold
classical fold `cfold_{θ_d} ∘ ⋯ ∘ cfold_{θ_1}(w)` at `ξ^{2^d}` depends only on the values of `w`
on `S(ξ) = {ζ ∈ D : ζ^{2^d} = ξ^{2^d}}`. -/
theorem cfoldUp_local {D : Subgroup Fˣ} (θ : ℕ → F) :
    ∀ (d : ℕ) (w w' : D → F) (ξ : D),
      (∀ ζ : D, ptAt ζ d = ptAt ξ d → w ζ = w' ζ) →
      cfoldUp θ w d (ptAt ξ d) = cfoldUp θ w' d (ptAt ξ d)
  | 0, _, _, ξ, h => h ξ rfl
  | d + 1, w, w', ξ, h => by
      show cwfold (θ d) (cfoldUp θ w d) (sqPt (ptAt ξ d)) =
        cwfold (θ d) (cfoldUp θ w' d) (sqPt (ptAt ξ d))
      apply cwfold_congr
      intro ζ' hζ'
      obtain ⟨ζ, rfl⟩ := ptAt_surjective (L := D) d ζ'
      apply cfoldUp_local θ d w w' ζ
      intro ζ'' h''
      apply h
      have e1 : ptAt ζ'' (d + 1) = sqPt (ptAt ζ'' d) := rfl
      have e2 : ptAt ξ (d + 1) = sqPt (ptAt ξ d) := rfl
      rw [e1, e2, h'']
      exact hζ'

end SumFRI
