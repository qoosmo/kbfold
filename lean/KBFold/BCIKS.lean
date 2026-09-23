/-
KBFold/BCIKS.lean
The correlated-agreement theorem of Ben-Sasson, Carmon, Ishai, Kopparty and Saraf in the
unique-decoding regime (Theorem 2.23 of the paper), stated as the single axiom of the project.

This is the only external result about codes used in the soundness analysis (§7); it is not
proved here.  The statement follows the paper's Theorem 2.23 word for word:
* `F` is a finite field (the paper's `𝔽 ⊇ 𝔽_q`; as everywhere in the project, the smooth domain
  is a subgroup `L ≤ Fˣ` of the field in which the words live, see `KBFold/Domain.lean`);
* `L` is a smooth domain of order `M = 2^μ` (Definition 2.14), `𝒞 = RS_F[L,d]` with
  `1 ≤ d ≤ M` (Definition 2.17) and rate `ρ = d/M`;
* `0 < δ ≤ (1-ρ)/2`;
* `S = {r ∈ F : Δ(u⁰ + r u¹, 𝒞) ≤ δ}`; `Δ(w, 𝒞) ≤ δ` is expressed by `DistLE` (some codeword
  within relative distance `δ`, which is equivalent since `𝒞` is finite and nonempty);
* conclusion: a set `L' ⊆ L` with `|L'| ≥ (1-δ)M` and codewords `ĉ⁰, ĉ¹ ∈ 𝒞` with `u⁰ = ĉ⁰`
  and `u¹ = ĉ¹` on `L'`.
-/
import KBFold.Domain

namespace KBFold

/-- **Theorem 2.23** ([BCIKS23, Theorem 4.1], correlated agreement in the unique-decoding regime).
Let `F` be a finite field, `L ≤ Fˣ` a smooth domain of order `M`, `𝒞 = RS_F[L,d]` with
`1 ≤ d ≤ M` and rate `ρ = d/M`, and `0 < δ ≤ (1-ρ)/2`.  Let `u⁰, u¹ ∈ F^L` and
`S = {r ∈ F : Δ(u⁰ + r u¹, 𝒞) ≤ δ}`.  If `|S| > M`, then there are a set `L' ⊆ L` with
`|L'| ≥ (1-δ)M` and codewords `ĉ⁰, ĉ¹ ∈ 𝒞` such that `u⁰` agrees with `ĉ⁰`, and `u¹` agrees
with `ĉ¹`, on `L'`.

(Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, "Proximity gaps for Reed–Solomon codes",
J. ACM 2023, Theorem 4.1, specialised to the evaluation set `D = L` and `d = k + 1`.)
This is the only axiom of the formalisation. -/
axiom bciks_unique {F : Type*} [Field F] [Fintype F] (L : Subgroup Fˣ) (μ : ℕ)
    (hL : IsSmoothDomain L μ) (d : ℕ) (hd : 1 ≤ d) (hdM : d ≤ Nat.card L)
    (δ : ℚ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - rate L d) / 2) (u0 u1 : L → F)
    (hS : Nat.card L < {r : F | DistLE (u0 + r • u1) (RS L d : Set (L → F)) δ}.ncard) :
    ∃ L' : Set L, (1 - δ) * Nat.card L ≤ L'.ncard ∧
      ∃ c0 ∈ RS L d, ∃ c1 ∈ RS L d, ∀ ξ ∈ L', u0 ξ = c0 ξ ∧ u1 ξ = c1 ξ

end KBFold
