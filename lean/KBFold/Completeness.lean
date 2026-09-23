/-
KBFold/Completeness.lean
§6.3 of the paper: the honest prover of `Π_eval` and Theorem 6.5 (completeness).

The honest prover (`honestProver`) for a table `f` with `n = m + ℓ` variables and the point
`z = catPt ℓ zp zs` sends
* the round polynomials `s_{i+1} = honS ℓ r f χ₀ i` of equation (6.1), computed from the
  restricted tables `f_i = res_{r≤i}(f)` and `χ_i = res_{r≤i}(χ₀)`, `χ₀ = (b ↦ eq(b,z))`;
* the oracles `w_j = fold_{r_j}(⋯ fold_{r_1}(w₀))` (`foldUp`);
* the final table `g = f_ℓ = res_{r≤ℓ}(f)`.
-/
import KBFold.Protocol

set_option autoImplicit false

open Polynomial Finset

namespace KBFold

variable {F : Type*} [Field F]

/-- The honest prover of §6.2 for the table `f` (with `n = m + ℓ` variables) and the point
`z = (zp_0, …, zp_{ℓ-1}, zs)`. -/
noncomputable def honestProver (L : Subgroup Fˣ) {m ℓ : ℕ} (f : Table F (m + ℓ)) (zp : ℕ → F)
    (zs : Fin m → F) : EvalProver F L m where
  s i r := honS ℓ r f (eqTable (catPt ℓ zp zs)) i
  orc j r := foldUp r (Enc L f) j
  g r := resSeq ℓ r f

section

variable {L : Subgroup Fˣ} {m ℓ : ℕ} (f : Table F (m + ℓ)) (zp : ℕ → F) (zs : Fin m → F)

/-- The honest prover's messages depend only on the earlier challenges. -/
theorem honestProver_causal : (honestProver L f zp zs).Causal :=
  ⟨fun i r r' h => honS_congr ℓ r r' _ _ i h, fun j _ _ h => foldUp_congr _ j h⟩

/-- **Lemma 6.4(2):** the honest round polynomials lie in `F[X]_{<3}`. -/
theorem honestProver_degOK : (honestProver L f zp zs).DegOK :=
  fun i r => natDegree_honS ℓ r f _ i

/-- The honest oracles are the successive folds of `Enc(f)`, and the verifier's word `w_ℓ` is the
`ℓ`-th fold (Corollary 5.9 with `μ = n + R ≥ ℓ`). -/
theorem honest_W {μ : ℕ} (hL : IsSmoothDomain L μ) (hℓ : ℓ ≤ μ) (r : ℕ → F) :
    ∀ j ≤ ℓ, (honestProver L f zp zs).W ℓ (Enc L f) r j = foldUp r (Enc L f) j
  | 0, _ => rfl
  | j + 1, hj => by
      simp only [EvalProver.W]
      split_ifs with h
      · subst h
        rw [foldUp_Enc hL hℓ r f]
        rfl
      · rfl

/-- The verifier's running values equal the honest values `σ_j = ∑_b f_j(b) χ_j(b)`. -/
theorem honest_vv (r : ℕ → F) :
    ∀ j ≤ ℓ, (honestProver L f zp zs).vv (mle f (catPt ℓ zp zs)) r j =
      honSig ℓ r f (eqTable (catPt ℓ zp zs)) j
  | 0, _ => (honest_sum_zero r zp zs f).symm
  | j + 1, hj => honS_eval ℓ r f _ j (by omega)

/-- The honest prover passes every check for every choice of challenges `r` and query points `ξ`,
when `w₀ = Enc(f)` and `v = f~(z)` (proof of Theorem 6.5).  Here `L` is a smooth domain of
order `2^μ` with `ℓ ≤ μ` (in the paper `μ = n + R ≥ n ≥ ℓ`). -/
theorem honest_accepts {μ : ℕ} (hL : IsSmoothDomain L μ) (hℓ : ℓ ≤ μ) {κ : ℕ} (r : ℕ → F)
    (ξ : Fin κ → L) :
    (honestProver L f zp zs).Accepts ℓ (Enc L f) zp zs (mle f (catPt ℓ zp zs)) r ξ := by
  refine ⟨?_, ?_, ?_⟩
  · -- sumcheck
    intro i hi
    rw [honest_vv f zp zs r i hi.le]
    exact honS_zero_add_one ℓ r f _ i hi
  · -- closure
    unfold EvalProver.ClosureOK
    rw [honest_vv f zp zs r ℓ le_rfl, honest_sum_last]
    rfl
  · -- queries
    intro t
    refine ⟨?_, ?_⟩
    · intro j hj
      unfold EvalProver.Chk
      rw [honest_W f zp zs hL hℓ r j hj.le, honest_W f zp zs hL hℓ r (j + 1) hj]
      rfl
    · intro h0
      subst h0
      rfl

/-- **Theorem 6.5 (completeness).** If `w₀ = Enc(f)`, `v = f~(z)` and the prover is honest, the
verifier accepts with probability `1` (over `(r, ξ) ∈ F^ℓ × L^κ`). -/
theorem completeness [Fintype F] [Fintype L] {μ : ℕ} (hL : IsSmoothDomain L μ) (hℓ : ℓ ≤ μ)
    (κ : ℕ) :
    evalAccProb (honestProver L f zp zs) ℓ κ (Enc L f) zp zs (mle f (catPt ℓ zp zs)) = 1 := by
  unfold evalAccProb
  have : (fun ω : (Fin ℓ → F) × (Fin κ → L) =>
      (honestProver L f zp zs).Accepts ℓ (Enc L f) zp zs (mle f (catPt ℓ zp zs)) (extR ω.1) ω.2)
      = fun _ => True := by
    funext ω
    simp only [eq_iff_iff, iff_true]
    exact honest_accepts f zp zs hL hℓ (extR ω.1) ω.2
  rw [this]
  haveI : Nonempty L := ⟨1⟩
  exact prob_true

end

end KBFold
