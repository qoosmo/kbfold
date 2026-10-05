/-
KBFold/BCIKSProof/Arithmetic.lean
Arithmetic lemma for the bciks_unique proof (BCIKS23 Theorem 4.1, step 0).

From `δ ≤ (1 - rate L d) / 2` and `DistLE w (RS L d) δ` we derive
`2 * hdist w c ≤ n - d` for some `c ∈ RS L d`. This replaces the need
for `e = ⌊δ*n⌋`.
-/
import KBFold.Domain

namespace KBFold

open Set

variable {F : Type*} [Field F] [Fintype F]

/-- Step 0: basic arithmetic from the rate inequality.

Given `δ ≤ (1 - rate L d) / 2` and `w : L → F` with `DistLE w (RS L d) δ`,
there exists `c ∈ RS L d` such that `2 * hdist w c ≤ n - d` where `n = Nat.card L`. -/
lemma arithmetic_ineqs (L : Subgroup Fˣ) (d : ℕ) (hd : 1 ≤ d) (hdM : d ≤ Nat.card L)
    (δ : ℚ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - rate L d) / 2) (w : L → F)
    (hDist : DistLE w (RS L d : Set (L → F)) δ) :
    ∃ c ∈ RS L d, 2 * hdist w c ≤ Nat.card L - d := by
  rcases hDist with ⟨c, hc, hrel⟩
  refine ⟨c, hc, ?_⟩
  have hn_pos : 0 < Nat.card L := Nat.card_pos
  have hM_pos : (0 : ℚ) < Nat.card L := by exact_mod_cast hn_pos
  have h_rate : rate L d = (d : ℚ) / Nat.card L := rfl
  rw [h_rate] at hδ
  -- hδ : δ ≤ (1 - (d : ℚ) / n) / 2
  -- Clear denominator: multiply by 2*n > 0 to get 2*δ*n ≤ n - d
  have h_ineq : 2 * (δ * (Nat.card L : ℚ)) ≤ (Nat.card L : ℚ) - (d : ℚ) := by
    have h_mul : 0 < 2 * (Nat.card L : ℚ) := by positivity
    -- Multiply hδ by 2*n
    have htemp := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 2 * (Nat.card L : ℚ))
    -- htemp : (2*n)*δ ≤ (2*n)*((1 - d/n)/2)
    -- RHS simplifies to n-d
    have hRHS : (2 * (Nat.card L : ℚ)) * ((1 - (d : ℚ) / (Nat.card L : ℚ)) / 2) =
        (Nat.card L : ℚ) - (d : ℚ) := by
      have hn_ne_zero : (Nat.card L : ℚ) ≠ 0 := by exact_mod_cast hn_pos.ne'
      field_simp [hn_ne_zero]
    -- LHS = 2*n*δ = 2*δ*n
    have hLHS : (2 * (Nat.card L : ℚ)) * δ = 2 * (δ * (Nat.card L : ℚ)) := by ring
    -- Combine
    calc
      2 * (δ * (Nat.card L : ℚ)) = (2 * (Nat.card L : ℚ)) * δ := by ring
      _ ≤ (2 * (Nat.card L : ℚ)) * ((1 - (d : ℚ) / (Nat.card L : ℚ)) / 2) := htemp
      _ = (Nat.card L : ℚ) - (d : ℚ) := hRHS
  -- From hrel: relDist w c ≤ δ, i.e. (hdist w c : ℚ) / n ≤ δ
  rw [relDist] at hrel
  -- hrel : (hdist w c : ℚ) / (Nat.card L : ℚ) ≤ δ
  -- Using div_le_iff₀ with positive denominator:
  have h_hdist_le : (hdist w c : ℚ) ≤ δ * (Nat.card L : ℚ) :=
    (div_le_iff₀ hM_pos).mp hrel
  -- Now: 2 * hdist ≤ 2 * δ * n ≤ n - d
  have h_2hdist_le_n_sub_d : (2 * hdist w c : ℚ) ≤ (Nat.card L : ℚ) - (d : ℚ) := by
    push_cast
    nlinarith
  -- Convert to ℕ: since both sides are integers, the rational inequality implies the ℕ inequality
  have h_2hdist_le_n_sub_d_nat : 2 * hdist w c ≤ Nat.card L - d := by
    -- We have h_2hdist_le_n_sub_d in ℚ. Since all terms are integers, we can cast to ℤ.
    have h_int : (2 * hdist w c : ℤ) ≤ (Nat.card L : ℤ) - (d : ℤ) := by
      exact_mod_cast h_2hdist_le_n_sub_d
    omega
  exact h_2hdist_le_n_sub_d_nat
