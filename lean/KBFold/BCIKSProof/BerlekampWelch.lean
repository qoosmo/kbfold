/-
KBFold/BCIKSProof/BerlekampWelch.lean
Berlekamp–Welch decoder for Reed–Solomon codes.
-/
import KBFold.Domain

namespace KBFold

open Polynomial
open Set

variable {F : Type*} [Field F]

/-- The Berlekamp–Welch decoder for Reed–Solomon codes. -/
lemma berlekamp_welch (L : Subgroup Fˣ) [Finite L] {d e : ℕ} (hd : 1 ≤ d) {P : F[X]}
    (hP : P ∈ degreeLT F d) (w : L → F) (he : hdist w (ev L P) ≤ e) :
    ∃ (E Q : F[X]), E.Monic ∧ E.natDegree = e ∧ Q.natDegree < e + d ∧
      ∀ ξ : L, Q.eval (xv ξ) = E.eval (xv ξ) * w ξ := by
  classical
  haveI : CommSemiring F := by infer_instance
  haveI : Nontrivial F := by infer_instance
  let I : Set L := disagreeSet w (ev L P)
  have hI_finite : Set.Finite I := Set.toFinite _
  let s := hI_finite.toFinset
  have hs_mem : ∀ ξ : L, ξ ∈ s ↔ ξ ∈ I := by
    intro ξ; simp [s]
  have hs_card : s.card ≤ e := by
    have h_eq : s.card = I.ncard :=
      (Set.ncard_eq_toFinset_card I hI_finite).symm
    rw [h_eq]
    dsimp [I, hdist]
    exact he
  let E : F[X] := X ^ (e - s.card) * (Finset.prod s fun ξ => (X - C (xv ξ)))
  have hE_monic : E.Monic := by
    refine Monic.mul (monic_X_pow _) ?_
    refine monic_prod_of_monic _ _ (fun ξ _ => ?_)
    exact monic_X_sub_C (xv ξ)
  have hE_natDegree : E.natDegree = e := by
    have h_pow : (X ^ (e - s.card)).natDegree = e - s.card :=
      natDegree_X_pow (R := F) (n := e - s.card)
    have h_prod : (∏ ξ ∈ s, (X - C (xv ξ))).natDegree = s.card := by
      have h_monic : ∀ ξ ∈ s, (X - C (xv ξ)).Monic := by
        intro ξ _; exact monic_X_sub_C _
      rw [natDegree_prod_of_monic h_monic]
      simp
    have h_monic_prod : (∏ ξ ∈ s, (X - C (xv ξ))).Monic :=
      monic_prod_of_monic _ _ (fun ξ _ => monic_X_sub_C _)
    have h_monic_pow : (X ^ (e - s.card)).Monic := monic_X_pow _
    rw [hE_monic.natDegree_eq_of_natDegree_le ?_]
    · rw [natDegree_mul h_monic_pow.ne_zero h_monic_prod.ne_zero, h_pow, h_prod]
      omega
    · rw [h_pow, h_prod]
      omega
  let Q : F[X] := E * P
  have h_sum_pos : 0 < e + d := by
    have : 0 < d := by omega
    omega
  have h_deg_P : P.natDegree < d := by
    rw [mem_degreeLT] at hP
    by_cases hPz : P = 0
    · rw [hPz, natDegree_zero]
      exact hd
    · exact ((natDegree_lt_iff_degree_lt hPz).mpr hP)
  have hQ_natDegree : Q.natDegree < e + d := by
    by_cases hP_zero : P = 0
    · dsimp [Q]
      rw [hP_zero, mul_zero, natDegree_zero]
      exact h_sum_pos
    · dsimp [Q]
      rw [natDegree_mul hE_monic.ne_zero hP_zero, hE_natDegree]
      omega
  have hQ_eq : ∀ ξ : L, Q.eval (xv ξ) = E.eval (xv ξ) * w ξ := by
    intro ξ
    by_cases hξ : ξ ∈ I
    · have hE_zero : E.eval (xv ξ) = 0 := by
        have hξs : ξ ∈ s := (hs_mem ξ).mpr hξ
        have h_factor : (X - C (xv ξ)) ∣ E := by
          refine Dvd.intro (X ^ (e - s.card) * ∏ η ∈ s.erase ξ, (X - C (xv η))) ?_
          dsimp [E]
          rw [← Finset.mul_prod_erase s (fun η => X - C (xv η)) hξs]
          ring
        rw [eval_eq_zero_of_dvd_of_eval_eq_zero h_factor]
        simp
      calc
        Q.eval (xv ξ) = (E * P).eval (xv ξ) := rfl
        _ = E.eval (xv ξ) * P.eval (xv ξ) := by rw [eval_mul]
        _ = 0 * P.eval (xv ξ) := by rw [hE_zero]
        _ = 0 := by simp
        _ = 0 * w ξ := by simp
        _ = E.eval (xv ξ) * w ξ := by rw [hE_zero]
    · have h_eq : w ξ = ev L P ξ := by
        dsimp [I, disagreeSet] at hξ
        simpa using hξ
      dsimp [Q]
      rw [eval_mul]
      simp [ev, h_eq]
  exact ⟨E, Q, hE_monic, hE_natDegree, hQ_natDegree, hQ_eq⟩
