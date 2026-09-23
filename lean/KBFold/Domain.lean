/-
KBFold/Domain.lean
Formalisation of §2.5 of the paper (smooth domains and Reed–Solomon codes):
Definition 2.14 (smooth domain), Lemma 2.15 (power maps), Definition 2.16 (fibres),
Definition 2.17 (Reed–Solomon codes), Lemma 2.18 (Hamming distance),
Lemma 2.19 (parameters of RS codes), and the even–odd split of words (Lemma 2.22).

Conventions.
* The paper takes the domain `L ≤ 𝔽_qˣ` and words with values in an extension `𝔽 ⊇ 𝔽_q`.
  Here everything is stated for a single field `F` and a subgroup `L ≤ Fˣ`; the paper's
  situation is recovered by mapping `L` into `Fˣ` along `𝔽_q → F` (this is injective, so it
  preserves the order and all statements below).  None of the results of this file
  needs `F` to be finite, except Lemma 2.15(1), which is about `𝔽_q`.
* The odd-characteristic hypothesis of the paper appears as `(2 : F) ≠ 0` where it is used;
  note that it is *implied* by the existence of a smooth domain of order `≥ 2`
  (`two_ne_zero_of_smooth`).
* Words on `L` are functions `L → F` (on the subtype `↥L`); the evaluation of a polynomial at
  `ξ : L` is `P.eval ((ξ : Fˣ) : F)`.
* The squared domain `L²` is `sqDom L = L.map (powMonoidHom 2)`, and the iterated domains
  `L^{2^j}` are `iterDom j L` (squaring `j` times; `iterDom_eq` identifies it with the image of
  the `2^j`-th power map).
-/
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Roots
import KBFold.Kernel

open Polynomial

namespace KBFold

variable {F : Type*} [Field F]

/-! ### Definition 2.14 (smooth domains) -/

/-- Definition 2.14: a smooth domain of order `2^μ` is a subgroup `L ≤ Fˣ` with `|L| = 2^μ`. -/
def IsSmoothDomain (L : Subgroup Fˣ) (μ : ℕ) : Prop := Nat.card L = 2 ^ μ

/-- Definition 2.14: the image `L^k = {ξ^k : ξ ∈ L}` of the `k`-th power map. -/
def powDom (L : Subgroup Fˣ) (k : ℕ) : Subgroup Fˣ := L.map (powMonoidHom k)

/-- Definition 2.14: the squared domain `L² = {ξ² : ξ ∈ L}` (image of the squaring map). -/
def sqDom (L : Subgroup Fˣ) : Subgroup Fˣ := powDom L 2

/-- The iterated squared domains: `iterDom 0 L = L`, `iterDom (j+1) L = iterDom j (L²)`.
By `iterDom_eq` this is `L^{2^j}` (Definition 2.14). -/
def iterDom : ℕ → Subgroup Fˣ → Subgroup Fˣ
  | 0, L => L
  | j + 1, L => iterDom j (sqDom L)

@[simp] lemma iterDom_zero (L : Subgroup Fˣ) : iterDom 0 L = L := rfl

lemma iterDom_succ (j : ℕ) (L : Subgroup Fˣ) : iterDom (j+1) L = iterDom j (sqDom L) := rfl

lemma mem_powDom {L : Subgroup Fˣ} {k : ℕ} {η : Fˣ} : η ∈ powDom L k ↔ ∃ ξ ∈ L, ξ ^ k = η :=
  Subgroup.mem_map

lemma powDom_powDom (L : Subgroup Fˣ) (a b : ℕ) : powDom (powDom L a) b = powDom L (a * b) := by
  unfold powDom
  rw [Subgroup.map_map]
  congr 1
  ext x; simp [pow_mul]

/-- Lemma 2.15(3): `(L^{2^j})² = L^{2^{j+1}}`; hence `iterDom j L = L^{2^j}`. -/
theorem iterDom_eq : ∀ (j : ℕ) (L : Subgroup Fˣ), iterDom j L = powDom L (2 ^ j)
  | 0, L => by
      simp only [iterDom_zero, pow_zero, powDom]
      conv_lhs => rw [← Subgroup.map_id L]
      congr 1
      ext x; simp
  | j + 1, L => by
      rw [iterDom_succ, iterDom_eq j, sqDom, powDom_powDom, pow_succ, mul_comm]

/-- Lemma 2.15(3), in the form `(L^{2^j})^2 = L^{2^{j+1}}`. -/
theorem sqDom_iterDom (j : ℕ) (L : Subgroup Fˣ) : sqDom (iterDom j L) = iterDom (j+1) L := by
  rw [iterDom_eq, iterDom_eq, sqDom, powDom_powDom, pow_succ]

/-! ### Lemma 2.15 (power maps on smooth domains) -/

/-- Every finite subgroup of `Fˣ` of order `e` consists of `e`-th roots of unity, hence *is*
the group of `e`-th roots of unity (uniqueness part of Lemma 2.15(1)). -/
theorem eq_rootsOfUnity_of_card {H : Subgroup Fˣ} {e : ℕ} (hH : Nat.card H = e) (he : e ≠ 0) :
    H = rootsOfUnity e F := by
  have hle : H ≤ rootsOfUnity e F := by
    intro x hx
    rw [mem_rootsOfUnity]
    have := pow_card_eq_one' (G := H) (x := ⟨x, hx⟩)
    rw [hH] at this
    simpa using congrArg Subtype.val this
  haveI : NeZero e := ⟨he⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hH, Nat.card_eq_fintype_card]
  exact card_rootsOfUnity F e

/-- Lemma 2.15(1), uniqueness: two subgroups of `Fˣ` of the same finite nonzero order are equal. -/
theorem subgroup_eq_of_card_eq {H K : Subgroup Fˣ} {e : ℕ} (hH : Nat.card H = e)
    (hK : Nat.card K = e) (he : e ≠ 0) : H = K := by
  rw [eq_rootsOfUnity_of_card hH he, eq_rootsOfUnity_of_card hK he]

/-- Lemma 2.15(1), cyclicity: every finite subgroup of `Fˣ` (in particular a smooth domain)
is cyclic. -/
theorem isCyclic_of_finite (L : Subgroup Fˣ) [Finite L] : IsCyclic L :=
  isCyclic_of_subgroup_isDomain ((Units.coeHom F).comp L.subtype)
    (fun _ _ h => Subtype.ext (Units.ext h))

/-- Lemma 2.15(1), existence: for a finite field `F` with `q` elements, `Fˣ` has a subgroup of
order `e` if and only if `e ∣ q - 1` (applied with `e = 2^μ`). -/
theorem exists_subgroup_card_iff [Fintype F] (e : ℕ) :
    (∃ H : Subgroup Fˣ, Nat.card H = e) ↔ e ∣ Fintype.card F - 1 := by
  have hU : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
  constructor
  · rintro ⟨H, rfl⟩
    rw [← hU]; exact Subgroup.card_subgroup_dvd_card H
  · intro hdvd
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
    have hpos : 0 < Nat.card Fˣ := Nat.card_pos
    rw [← hU] at hdvd
    refine ⟨Subgroup.zpowers (g ^ (orderOf g / e)), ?_⟩
    rw [Nat.card_zpowers, orderOf_pow_orderOf_div (by rw [hg]; omega) (by rw [hg]; exact hdvd)]

/-- A smooth domain is finite. -/
theorem IsSmoothDomain.finite {L : Subgroup Fˣ} {μ : ℕ} (h : IsSmoothDomain L μ) : Finite L :=
  Nat.finite_of_card_ne_zero (by rw [h]; exact pow_ne_zero _ two_ne_zero)

/-- The `k`-th power map restricted to `L`, as a homomorphism `L →* Fˣ`. -/
def powHom (L : Subgroup Fˣ) (k : ℕ) : L →* Fˣ := (powMonoidHom k).comp L.subtype

lemma powHom_apply (L : Subgroup Fˣ) (k : ℕ) (ξ : L) : powHom L k ξ = (ξ : Fˣ) ^ k := rfl

lemma range_powHom (L : Subgroup Fˣ) (k : ℕ) : (powHom L k).range = powDom L k := by
  rw [powHom, MonoidHom.range_comp, Subgroup.range_subtype]; rfl

lemma card_range_mul_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nat.card G = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

lemma card_ker_powHom_le (L : Subgroup Fˣ) {k : ℕ} (hk : k ≠ 0) :
    Nat.card (powHom L k).ker ≤ k := by
  haveI : NeZero k := ⟨hk⟩
  let g : (powHom L k).ker → rootsOfUnity k F := fun x =>
    ⟨((x : L) : Fˣ), by
      rw [mem_rootsOfUnity]; have := x.2; rw [MonoidHom.mem_ker, powHom_apply] at this; exact this⟩
  have hg : Function.Injective g := by
    intro a b h
    have := congrArg (fun x : rootsOfUnity k F => (x : Fˣ)) h
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card (powHom L k).ker ≤ Nat.card (rootsOfUnity k F) := Nat.card_le_card_of_injective g hg
    _ = Fintype.card (rootsOfUnity k F) := Nat.card_eq_fintype_card
    _ ≤ k := card_rootsOfUnity F k

/-- Lemma 2.15(2): for a smooth domain `L` of order `2^μ` and `j ≤ μ`, the image `L^{2^j}`
of the `2^j`-th power map has order `2^{μ-j}`, and the kernel of that map has order `2^j`. -/
theorem card_powDom_and_ker {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) {j : ℕ}
    (hj : j ≤ μ) :
    Nat.card (powDom L (2 ^ j)) = 2 ^ (μ - j) ∧ Nat.card (powHom L (2 ^ j)).ker = 2 ^ j := by
  haveI := hL.finite
  have hker := card_ker_powHom_le L (k := 2 ^ j) (pow_ne_zero _ two_ne_zero)
  haveI : NeZero (2 ^ (μ - j)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hle : powDom L (2 ^ j) ≤ rootsOfUnity (2 ^ (μ - j)) F := by
    intro η hη
    obtain ⟨ξ, hξ, rfl⟩ := mem_powDom.1 hη
    rw [mem_rootsOfUnity, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hj]
    have := pow_card_eq_one' (G := L) (x := ⟨ξ, hξ⟩)
    rw [hL] at this
    simpa using congrArg Subtype.val this
  have hran : Nat.card (powDom L (2 ^ j)) ≤ 2 ^ (μ - j) := by
    calc Nat.card (powDom L (2 ^ j)) ≤ Nat.card (rootsOfUnity (2 ^ (μ - j)) F) :=
          Subgroup.card_le_of_le hle
      _ = Fintype.card (rootsOfUnity (2 ^ (μ - j)) F) := Nat.card_eq_fintype_card
      _ ≤ 2 ^ (μ - j) := card_rootsOfUnity F _
  have hprod := card_range_mul_card_ker (powHom L (2 ^ j))
  rw [range_powHom, hL] at hprod
  have htot : 2 ^ μ = 2 ^ (μ - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
  set a := Nat.card (powDom L (2 ^ j))
  set b := Nat.card (powHom L (2 ^ j)).ker
  have hA : 0 < 2 ^ (μ - j) := by positivity
  have hB : 0 < 2 ^ j := by positivity
  have h1 : a * b ≤ a * 2 ^ j := Nat.mul_le_mul_left _ hker
  have h2 : a * 2 ^ j ≤ 2 ^ (μ - j) * 2 ^ j := Nat.mul_le_mul_right _ hran
  have ha : a = 2 ^ (μ - j) := by
    apply Nat.eq_of_mul_eq_mul_right hB; omega
  refine ⟨ha, ?_⟩
  rw [ha] at hprod
  apply Nat.eq_of_mul_eq_mul_left hA; omega

/-- Lemma 2.15(2): `L^{2^j}` is the smooth domain of order `2^{μ-j}`. -/
theorem IsSmoothDomain.powDom_smooth {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) {j : ℕ}
    (hj : j ≤ μ) : IsSmoothDomain (powDom L (2 ^ j)) (μ - j) :=
  (card_powDom_and_ker hL hj).1

/-- Lemma 2.15(2)–(3): the iterated squared domain `L^{2^j}` has order `2^{μ-j}`. -/
theorem IsSmoothDomain.iterDom_smooth {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) {j : ℕ}
    (hj : j ≤ μ) : IsSmoothDomain (iterDom j L) (μ - j) := by
  rw [iterDom_eq]; exact hL.powDom_smooth hj

/-- Lemma 2.15(2) with `j = 1`: `L²` has order `2^{μ-1}`. -/
theorem IsSmoothDomain.sqDom_smooth {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) (hμ : 1 ≤ μ) :
    IsSmoothDomain (sqDom L) (μ - 1) := by
  have := hL.powDom_smooth hμ; simpa [KBFold.sqDom] using this

/-- Lemma 2.15(2): every element of `L^{2^j}` has exactly `2^j` preimages in `L` under the
`2^j`-th power map. -/
theorem card_powHom_fibre {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) {j : ℕ}
    (hj : j ≤ μ) {η : Fˣ} (hη : η ∈ powDom L (2 ^ j)) :
    Nat.card (powHom L (2 ^ j) ⁻¹' {η}) = 2 ^ j := by
  rw [← range_powHom] at hη
  obtain ⟨ξ0, rfl⟩ := hη
  rw [Nat.card_congr ((powHom L (2 ^ j)).fiberEquivKer ξ0)]
  exact (card_powDom_and_ker hL hj).2

/-- In a field, `ζ² = ξ²` iff `ζ = ±ξ` (units version). -/
lemma units_sq_eq_sq_iff (ζ ξ : Fˣ) : ζ ^ 2 = ξ ^ 2 ↔ ζ = ξ ∨ ζ = -ξ := by
  constructor
  · intro h
    have h' : (ζ : F) ^ 2 = (ξ : F) ^ 2 := by
      have := congrArg (fun u : Fˣ => (u : F)) h; simpa using this
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h' with h1 | h1
    · left; exact Units.ext h1
    · right; exact Units.ext (by simpa using h1)
  · rintro (rfl | rfl)
    · rfl
    · exact neg_sq ξ

/-- If `(2 : F) ≠ 0` then `-ξ ≠ ξ` for every unit `ξ`. -/
lemma units_neg_ne_self (h2 : (2 : F) ≠ 0) (ξ : Fˣ) : -ξ ≠ ξ := by
  intro h
  have h' : -(ξ : F) = ξ := by have := congrArg (fun u : Fˣ => (u : F)) h; simpa using this
  have : (2 : F) * ξ = 0 := by linear_combination -h'
  rcases mul_eq_zero.1 this with h0 | h0
  · exact h2 h0
  · exact ξ.ne_zero h0

/-- Lemma 2.15(4): if `μ ≥ 1` then `-1 ∈ L` and `-1 ≠ 1`. -/
theorem neg_one_mem_and_ne {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) (hμ : 1 ≤ μ) :
    (-1 : Fˣ) ∈ L ∧ (-1 : F) ≠ 1 := by
  haveI := hL.finite
  have hk := (card_powDom_and_ker hL hμ).2
  rw [pow_one] at hk
  haveI : Nontrivial (powHom L 2).ker := by
    rw [← Finite.one_lt_card_iff_nontrivial, hk]; norm_num
  obtain ⟨x, hx⟩ := exists_ne (1 : (powHom L 2).ker)
  have hx2 : ((x : L) : Fˣ) ^ 2 = 1 := by
    have := x.2; rwa [MonoidHom.mem_ker, powHom_apply] at this
  have hx1 : ((x : L) : Fˣ) ≠ 1 := by
    intro h; apply hx; apply Subtype.ext; apply Subtype.ext; simpa using h
  have hF : (((x : L) : Fˣ) : F) = -1 := by
    have h2 : (((x : L) : Fˣ) : F) * (((x : L) : Fˣ) : F) = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) hx2; simpa [sq] using this
    rcases mul_self_eq_one_iff.1 h2 with h | h
    · exact absurd (Units.ext (by simpa using h)) hx1
    · exact h
  have hxeq : ((x : L) : Fˣ) = -1 := Units.ext (by simpa using hF)
  refine ⟨hxeq ▸ (x : L).2, ?_⟩
  intro h; apply hx1; rw [hxeq]; exact Units.ext (by simpa using h)

/-- Lemma 2.15(4): `-1 ∈ L` when `μ ≥ 1`. -/
theorem IsSmoothDomain.neg_one_mem {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ)
    (hμ : 1 ≤ μ) : (-1 : Fˣ) ∈ L := (neg_one_mem_and_ne hL hμ).1

/-- The existence of a smooth domain of order `≥ 2` forces odd characteristic: `(2 : F) ≠ 0`. -/
theorem two_ne_zero_of_smooth {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ)
    (hμ : 1 ≤ μ) : (2 : F) ≠ 0 := by
  intro h
  apply (neg_one_mem_and_ne hL hμ).2
  linear_combination -h

/-! ### Points of `L`, `-ξ`, `ξ²`, and fibres (Lemma 2.15(4), Definition 2.16) -/

section Points

variable {L : Subgroup Fˣ}

/-- The point `-ξ` of `L` (Lemma 2.15(4)).  To keep the definition total it returns `ξ` when
`-ξ ∉ L`; under `-1 ∈ L` it is always `-ξ` (`coe_negPt`). -/
noncomputable def negPt (ξ : L) : L := by
  classical exact if h : -(ξ : Fˣ) ∈ L then ⟨-(ξ : Fˣ), h⟩ else ξ

lemma neg_mem_of_neg_one_mem (hL : (-1 : Fˣ) ∈ L) (ξ : L) : -(ξ : Fˣ) ∈ L := by
  rw [← neg_one_mul]; exact L.mul_mem hL ξ.2

@[simp] lemma coe_negPt (hL : (-1 : Fˣ) ∈ L) (ξ : L) : ((negPt ξ : L) : Fˣ) = -(ξ : Fˣ) := by
  simp [negPt, neg_mem_of_neg_one_mem hL ξ]

lemma val_negPt (hL : (-1 : Fˣ) ∈ L) (ξ : L) : (((negPt ξ : L) : Fˣ) : F) = -(((ξ : L) : Fˣ) : F) := by
  rw [coe_negPt hL]; simp

lemma negPt_negPt (hL : (-1 : Fˣ) ∈ L) (ξ : L) : negPt (negPt ξ) = ξ := by
  apply Subtype.ext; rw [coe_negPt hL, coe_negPt hL, neg_neg]

lemma negPt_sq (ξ : L) : ((negPt ξ : L) : Fˣ) ^ 2 = (ξ : Fˣ) ^ 2 := by
  unfold negPt; split_ifs <;> simp

/-- Lemma 2.15(4): `-ξ ≠ ξ` (odd characteristic). -/
lemma negPt_ne (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (ξ : L) : negPt ξ ≠ ξ := by
  intro h
  apply units_neg_ne_self h2 (ξ : Fˣ)
  rw [← coe_negPt hL, h]

/-- The point `ξ²` of `L²`. -/
def sqPt (ξ : L) : sqDom L := ⟨(ξ : Fˣ) ^ 2, ⟨ξ, ξ.2, rfl⟩⟩

@[simp] lemma coe_sqPt (ξ : L) : ((sqPt ξ : sqDom L) : Fˣ) = (ξ : Fˣ) ^ 2 := rfl

lemma val_sqPt (ξ : L) : (((sqPt ξ : sqDom L) : Fˣ) : F) = (((ξ : L) : Fˣ) : F) ^ 2 := by
  simp

/-- A chosen square root in `L` of a point of `L²`. -/
noncomputable def sqrtPt (η : sqDom L) : L :=
  ⟨_, (mem_powDom.1 η.2).choose_spec.1⟩

@[simp] lemma sqPt_sqrtPt (η : sqDom L) : sqPt (sqrtPt η) = η :=
  Subtype.ext (mem_powDom.1 η.2).choose_spec.2

lemma sqPt_negPt (ξ : L) : sqPt (negPt ξ) = sqPt ξ := Subtype.ext (negPt_sq ξ)

/-- Lemma 2.15(4): the square roots in `L` of `ξ²` are exactly `ξ` and `-ξ`. -/
theorem sqPt_eq_iff (hL : (-1 : Fˣ) ∈ L) (ζ ξ : L) : sqPt ζ = sqPt ξ ↔ ζ = ξ ∨ ζ = negPt ξ := by
  constructor
  · intro h
    have h' : (ζ : Fˣ) ^ 2 = (ξ : Fˣ) ^ 2 := congrArg Subtype.val h
    rcases (units_sq_eq_sq_iff _ _).1 h' with h1 | h1
    · left; exact Subtype.ext h1
    · right; apply Subtype.ext; rw [coe_negPt hL]; exact h1
  · rintro (rfl | rfl)
    · rfl
    · exact sqPt_negPt ξ

/-- Lemma 2.15(2) with `j = 1`: squaring `L → L²` is surjective. -/
lemma sqPt_surjective : Function.Surjective (sqPt : L → sqDom L) :=
  fun η => ⟨sqrtPt η, sqPt_sqrtPt η⟩

/-- `L²` is finite when `L` is. -/
instance sqDom_finite [Finite L] : Finite (sqDom L) := Finite.of_surjective _ sqPt_surjective

/-- The iterated squared domains `L^{2^j}` are finite when `L` is. -/
theorem iterDom_finite : ∀ (j : ℕ) (L : Subgroup Fˣ) [Finite L], Finite (iterDom j L)
  | 0, _, _ => ‹_›
  | j + 1, L, _ => iterDom_finite j (sqDom L)

/-- Definition 2.16: the fibre over `η ∈ L²` is the set of its square roots in `L`. -/
def fibre (η : sqDom L) : Set L := {ξ | sqPt ξ = η}

lemma mem_fibre {η : sqDom L} {ξ : L} : ξ ∈ fibre η ↔ sqPt ξ = η := Iff.rfl

/-- Definition 2.16: the fibre over `ξ²` is `{ξ, -ξ}`. -/
theorem fibre_sqPt (hL : (-1 : Fˣ) ∈ L) (ξ : L) : fibre (sqPt ξ) = {ξ, negPt ξ} := by
  ext ζ; simp [mem_fibre, sqPt_eq_iff hL]

/-- Definition 2.16: every fibre has exactly two points. -/
theorem ncard_fibre (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (η : sqDom L) :
    (fibre η).ncard = 2 := by
  rw [← sqPt_sqrtPt η, fibre_sqPt hL, Set.ncard_pair (negPt_ne hL h2 _).symm]

/-- Definition 2.16: the fibres partition `L` (each point lies in exactly one fibre). -/
theorem existsUnique_fibre (ξ : L) : ∃! η : sqDom L, ξ ∈ fibre η :=
  ⟨sqPt ξ, rfl, fun _ h => h.symm⟩

lemma sqrtPt_mem_fibre (η : sqDom L) : sqrtPt η ∈ fibre η := sqPt_sqrtPt η

lemma negPt_mem_fibre {η : sqDom L} {ξ : L} (h : ξ ∈ fibre η) : negPt ξ ∈ fibre η := by
  rw [mem_fibre, sqPt_negPt]; exact h

/-- Definition 2.16: there are `M/2` fibres (the order of `L²` is `2^{μ-1}`). -/
theorem card_sqDom {μ : ℕ} (hL : IsSmoothDomain L μ) (hμ : 1 ≤ μ) :
    Nat.card (sqDom L) * 2 = Nat.card L := by
  rw [hL.sqDom_smooth hμ, hL, ← pow_succ, Nat.sub_add_cancel hμ]

end Points

/-! ### Lemma 2.18 (Hamming distance) -/

section Hamming

variable {ι β : Type*}

/-- The set of positions where two words differ. -/
def disagreeSet (w w' : ι → β) : Set ι := {i | w i ≠ w' i}

/-- The set of positions where two words agree (Definition 2.17). -/
def agreeSet (w w' : ι → β) : Set ι := {i | w i = w' i}

/-- The (absolute) Hamming distance: number of positions where two words differ. -/
noncomputable def hdist (w w' : ι → β) : ℕ := (disagreeSet w w').ncard

/-- Definition 2.17: the relative Hamming distance `Δ(w,w') = |{ξ : w(ξ) ≠ w'(ξ)}| / M`. -/
noncomputable def relDist (w w' : ι → β) : ℚ := (hdist w w' : ℚ) / Nat.card ι

/-- Definition 2.17: `Δ(w, 𝒞) ≤ δ`, i.e. some element of `𝒞` is within relative distance `δ`
of `w`.  For a finite nonempty `𝒞` the minimum in the paper's `Δ(w,𝒞) = min_c Δ(w,c)` is
attained, so this is equivalent to `Δ(w,𝒞) ≤ δ`. -/
def DistLE (w : ι → β) (C : Set (ι → β)) (δ : ℚ) : Prop := ∃ c ∈ C, relDist w c ≤ δ

lemma agreeSet_eq_compl (w w' : ι → β) : agreeSet w w' = (disagreeSet w w')ᶜ := by
  ext i; simp [agreeSet, disagreeSet]

lemma agree_add_hdist [Finite ι] (w w' : ι → β) :
    (agreeSet w w').ncard + hdist w w' = Nat.card ι := by
  rw [agreeSet_eq_compl, hdist, add_comm, Set.ncard_add_ncard_compl]

/-- Lemma 2.18 (symmetry). -/
lemma hdist_comm (w w' : ι → β) : hdist w w' = hdist w' w := by
  unfold hdist disagreeSet; simp_rw [ne_comm]

@[simp] lemma hdist_self (w : ι → β) : hdist w w = 0 := by simp [hdist, disagreeSet]

/-- Lemma 2.18 (definiteness). -/
lemma hdist_eq_zero_iff [Finite ι] {w w' : ι → β} : hdist w w' = 0 ↔ w = w' := by
  rw [hdist, Set.ncard_eq_zero]
  constructor
  · intro h; funext i; by_contra hi
    have : i ∈ disagreeSet w w' := hi
    rw [h] at this; exact this
  · rintro rfl; simp [disagreeSet]

/-- Lemma 2.18 (triangle inequality). -/
lemma hdist_triangle [Finite ι] (w w' w'' : ι → β) :
    hdist w w'' ≤ hdist w w' + hdist w' w'' := by
  unfold hdist
  calc (disagreeSet w w'').ncard ≤ (disagreeSet w w' ∪ disagreeSet w' w'').ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        intro i (hi : w i ≠ w'' i)
        by_contra hc
        simp only [Set.mem_union, disagreeSet, Set.mem_setOf_eq, not_or, not_not] at hc
        exact hi (hc.1.trans hc.2)
    _ ≤ _ := Set.ncard_union_le _ _

lemma relDist_comm (w w' : ι → β) : relDist w w' = relDist w' w := by
  rw [relDist, relDist, hdist_comm]

@[simp] lemma relDist_self (w : ι → β) : relDist w w = 0 := by simp [relDist]

lemma relDist_nonneg (w w' : ι → β) : 0 ≤ relDist w w' := by
  unfold relDist; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Lemma 2.18: `Δ` is definite. -/
lemma relDist_eq_zero_iff [Finite ι] [Nonempty ι] {w w' : ι → β} : relDist w w' = 0 ↔ w = w' := by
  have : (Nat.card ι : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [relDist, div_eq_zero_iff, or_iff_left this, Nat.cast_eq_zero, hdist_eq_zero_iff]

/-- Lemma 2.18: `Δ` satisfies the triangle inequality. -/
lemma relDist_triangle [Finite ι] (w w' w'' : ι → β) :
    relDist w w'' ≤ relDist w w' + relDist w' w'' := by
  unfold relDist
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hdist_triangle w w' w''

/-- Lemma 2.18, agreement form (natural numbers): the agreements of `w,w'` and of `w',w''`
exceed the agreement of `w,w''` by at most `M`. -/
lemma agree_trans [Finite ι] (w w' w'' : ι → β) :
    (agreeSet w w').ncard + (agreeSet w' w'').ncard ≤ (agreeSet w w'').ncard + Nat.card ι := by
  have h1 := agree_add_hdist w w'
  have h2 := agree_add_hdist w' w''
  have h3 := agree_add_hdist w w''
  have h4 := hdist_triangle w w' w''
  omega

/-- Lemma 2.18: if `w` agrees with `w'` on at least `αM` points and `w'` agrees with `w''`
on at least `βM` points, then `w` agrees with `w''` on at least `(α+β-1)M` points. -/
theorem agree_trans_frac [Finite ι] (w w' w'' : ι → β) (α β' : ℚ)
    (h1 : α * Nat.card ι ≤ (agreeSet w w').ncard) (h2 : β' * Nat.card ι ≤ (agreeSet w' w'').ncard) :
    (α + β' - 1) * Nat.card ι ≤ (agreeSet w w'').ncard := by
  have h := agree_trans w w' w''
  have h' : ((agreeSet w w').ncard : ℚ) + (agreeSet w' w'').ncard
      ≤ (agreeSet w w'').ncard + Nat.card ι := by exact_mod_cast h
  nlinarith

end Hamming

/-! ### Definition 2.17 (Reed–Solomon codes) -/

section RS

variable (L : Subgroup Fˣ)

/-- Definition 2.17: the evaluation map `ev_L : F[X] → F^L`. -/
def ev (P : F[X]) : L → F := fun ξ => P.eval (((ξ : L) : Fˣ) : F)

/-- Definition 2.17: `ev_L` as an `F`-linear map. -/
noncomputable def evLin : F[X] →ₗ[F] (L → F) where
  toFun := ev L
  map_add' P Q := by funext ξ; simp [ev]
  map_smul' a P := by funext ξ; simp [ev]

@[simp] lemma evLin_apply (P : F[X]) : evLin L P = ev L P := rfl

lemma ev_add (P Q : F[X]) : ev L (P + Q) = ev L P + ev L Q := (evLin L).map_add P Q

lemma ev_C_mul (a : F) (P : F[X]) : ev L (C a * P) = a • ev L P := by
  funext ξ; simp [ev]

/-- Definition 2.17: the Reed–Solomon code `RS[L,d] = ev_L(F[X]_{<d})`. -/
noncomputable def RS (d : ℕ) : Submodule F (L → F) := (degreeLT F d).map (evLin L)

variable {L}

lemma mem_RS {d : ℕ} {c : L → F} : c ∈ RS L d ↔ ∃ P ∈ degreeLT F d, ev L P = c := by
  simp [RS]

lemma ev_mem_RS {d : ℕ} {P : F[X]} (hP : P ∈ degreeLT F d) : ev L P ∈ RS L d :=
  mem_RS.2 ⟨P, hP, rfl⟩

/-- Definition 2.17: the rate `ρ = d/M`. -/
noncomputable def rate (L : Subgroup Fˣ) (d : ℕ) : ℚ := (d : ℚ) / Nat.card L

lemma degreeLT_mono' {m n : ℕ} (h : m ≤ n) {P : F[X]} (hP : P ∈ degreeLT F m) :
    P ∈ degreeLT F n := by
  rw [mem_degreeLT] at *
  exact lt_of_lt_of_le hP (by exact_mod_cast h)

/-! ### Lemma 2.19 (parameters of Reed–Solomon codes) -/

/-- Lemma 2.1 / Lemma 2.19 core: two polynomials of `F[X]_{<d}` whose evaluations agree on at
least `d` points of `L` are equal. -/
theorem eq_of_le_agree [Finite L] {d : ℕ} {P Q : F[X]} (hP : P ∈ degreeLT F d)
    (hQ : Q ∈ degreeLT F d) (h : d ≤ (agreeSet (ev L P) (ev L Q)).ncard) : P = Q := by
  classical
  have hR : P - Q ∈ degreeLT F d := Submodule.sub_mem _ hP hQ
  by_contra hne
  have hR0 : P - Q ≠ 0 := sub_ne_zero.2 hne
  have hdeg : (P - Q).natDegree < d := by
    rw [mem_degreeLT] at hR
    exact (natDegree_lt_iff_degree_lt hR0).2 hR
  let S := agreeSet (ev L P) (ev L Q)
  letI : Fintype S := Fintype.ofFinite S
  apply hR0
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (P - Q)
    (f := fun i : S => (((i : L) : Fˣ) : F)) ?_ ?_ ?_
  · intro a b hab
    exact Subtype.ext (Subtype.ext (Units.ext hab))
  · intro i
    have := i.2
    simp only [S, agreeSet, Set.mem_setOf_eq, ev] at this
    simp [eval_sub, this]
  · rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]; exact lt_of_lt_of_le hdeg h

/-- Lemma 2.19(1): `ev_L` is injective on `F[X]_{<d}` when `d ≤ M`. -/
theorem ev_injOn [Finite L] {d : ℕ} (hd : d ≤ Nat.card L) :
    Set.InjOn (ev L) (degreeLT F d : Set F[X]) := by
  intro P hP Q hQ h
  apply eq_of_le_agree (L := L) hP hQ
  have : agreeSet (ev L P) (ev L Q) = Set.univ := by
    ext ξ; simp [agreeSet, h]
  rw [this, Set.ncard_univ L]; exact hd

/-- Lemma 2.19(1): `ev_L : F[X]_{<d} → RS[L,d]` is a linear bijection. -/
noncomputable def rsEquiv [Finite L] {d : ℕ} (hd : d ≤ Nat.card L) :
    degreeLT F d ≃ₗ[F] RS L d :=
  LinearEquiv.ofBijective ((evLin L ∘ₗ (degreeLT F d).subtype).codRestrict (RS L d)
      (fun P => ev_mem_RS P.2))
    ⟨fun P Q h => Subtype.ext (ev_injOn hd P.2 Q.2 (congrArg Subtype.val h)),
     fun c => by
      obtain ⟨P, hP, hc⟩ := mem_RS.1 c.2
      exact ⟨⟨P, hP⟩, Subtype.ext hc⟩⟩

/-- Lemma 2.19(1): the polynomial `P_c ∈ F[X]_{<M}` with `ev_L(P_c) = c` (and `0` if there is
none).  It is defined without reference to a degree bound `d`; see `polyOf_spec`. -/
noncomputable def polyOf (c : L → F) : F[X] := by
  classical
  exact if h : ∃ P ∈ degreeLT F (Nat.card L), ev L P = c then h.choose else 0

/-- Lemma 2.19(1): `P_{ev(P)} = P` for `P ∈ F[X]_{<M}`. -/
theorem polyOf_ev [Finite L] {P : F[X]} (hP : P ∈ degreeLT F (Nat.card L)) :
    polyOf (ev L P) = P := by
  have h : ∃ Q ∈ degreeLT F (Nat.card L), ev L Q = ev L P := ⟨P, hP, rfl⟩
  simp only [polyOf, dif_pos h]
  exact ev_injOn le_rfl h.choose_spec.1 hP h.choose_spec.2

/-- Lemma 2.19(1): for `c ∈ RS[L,d]` with `d ≤ M`, `P_c ∈ F[X]_{<d}` and `ev_L(P_c) = c`;
`P_c` does not depend on `d`. -/
theorem polyOf_spec [Finite L] {d : ℕ} (hd : d ≤ Nat.card L) {c : L → F} (hc : c ∈ RS L d) :
    polyOf c ∈ degreeLT F d ∧ ev L (polyOf c) = c := by
  obtain ⟨P, hP, rfl⟩ := mem_RS.1 hc
  rw [polyOf_ev (degreeLT_mono' hd hP)]
  exact ⟨hP, rfl⟩

/-- Lemma 2.19(1): `P_c` is the unique polynomial of `F[X]_{<d}` evaluating to `c`. -/
theorem polyOf_unique [Finite L] {d : ℕ} (hd : d ≤ Nat.card L) {P : F[X]}
    (hP : P ∈ degreeLT F d) {c : L → F} (hc : ev L P = c) : polyOf c = P := by
  subst hc; exact polyOf_ev (degreeLT_mono' hd hP)

/-- Lemma 2.19(2): two distinct codewords of `RS[L,d]` agree on at most `d - 1` points. -/
theorem RS_agree_lt [Finite L] {d : ℕ} {c c' : L → F} (hc : c ∈ RS L d) (hc' : c' ∈ RS L d)
    (hne : c ≠ c') : (agreeSet c c').ncard < d := by
  obtain ⟨P, hP, rfl⟩ := mem_RS.1 hc
  obtain ⟨Q, hQ, rfl⟩ := mem_RS.1 hc'
  by_contra h
  exact hne (congrArg (ev L) (eq_of_le_agree hP hQ (not_lt.1 h)))

/-- Lemma 2.19(2): distinct codewords are at Hamming distance `≥ M - d + 1`. -/
theorem RS_hdist [Finite L] {d : ℕ} {c c' : L → F} (hc : c ∈ RS L d) (hc' : c' ∈ RS L d)
    (hne : c ≠ c') : Nat.card L + 1 ≤ hdist c c' + d := by
  have h1 := RS_agree_lt hc hc' hne
  have h2 := agree_add_hdist c c'
  omega

/-- Lemma 2.19(2): `Δ(c,c') ≥ 1 - (d-1)/M` for distinct codewords. -/
theorem RS_relDist [Finite L] {d : ℕ} {c c' : L → F} (hc : c ∈ RS L d) (hc' : c' ∈ RS L d)
    (hne : c ≠ c') : 1 - ((d : ℚ) - 1) / Nat.card L ≤ relDist c c' := by
  have h := RS_hdist hc hc' hne
  have hM : (0 : ℚ) < Nat.card L := by
    have : Nonempty L := ⟨1⟩
    exact_mod_cast Nat.card_pos
  rw [relDist, sub_le_iff_le_add, ← add_div, le_div_iff₀ hM, one_mul]
  have : ((Nat.card L : ℕ) : ℚ) + 1 ≤ (hdist c c' : ℚ) + d := by exact_mod_cast h
  linarith

/-- Lemma 2.19(2): `Δ(c,c') > 1 - ρ` for distinct codewords. -/
theorem RS_relDist_gt [Finite L] {d : ℕ} {c c' : L → F} (hc : c ∈ RS L d) (hc' : c' ∈ RS L d)
    (hne : c ≠ c') : 1 - rate L d < relDist c c' := by
  have h := RS_relDist hc hc' hne
  have hM : (0 : ℚ) < Nat.card L := by
    have : Nonempty L := ⟨1⟩
    exact_mod_cast Nat.card_pos
  refine lt_of_lt_of_le ?_ h
  rw [rate]
  have : ((d : ℚ) - 1) / Nat.card L < (d : ℚ) / Nat.card L :=
    div_lt_div_of_pos_right (by linarith) hM
  linarith

/-- Lemma 2.19(3): if `2δ < 1 - (d-1)/M`, every word is within relative distance `δ` of at most
one codeword. -/
theorem RS_unique_decoding [Finite L] {d : ℕ} (δ : ℚ)
    (hδ : 2 * δ < 1 - ((d : ℚ) - 1) / Nat.card L) (w : L → F) {c c' : L → F}
    (hc : c ∈ RS L d) (hc' : c' ∈ RS L d) (h1 : relDist w c ≤ δ) (h2 : relDist w c' ≤ δ) :
    c = c' := by
  by_contra hne
  have h := RS_relDist hc hc' hne
  have ht := relDist_triangle c w c'
  rw [relDist_comm c w] at ht
  linarith

/-- Lemma 2.19(3): `δ ≤ (1-ρ)/2` implies `2δ < 1 - (d-1)/M`. -/
theorem half_one_sub_rate_lt [Finite L] (d : ℕ) {δ : ℚ} (hδ : δ ≤ (1 - rate L d) / 2) :
    2 * δ < 1 - ((d : ℚ) - 1) / Nat.card L := by
  have hM : (0 : ℚ) < Nat.card L := by
    have : Nonempty L := ⟨1⟩
    exact_mod_cast Nat.card_pos
  rw [rate] at hδ
  have : ((d : ℚ) - 1) / Nat.card L < (d : ℚ) / Nat.card L :=
    div_lt_div_of_pos_right (by linarith) hM
  linarith

/-- Lemma 2.19(3) with `δ ≤ (1-ρ)/2`. -/
theorem RS_unique_decoding' [Finite L] {d : ℕ} (δ : ℚ) (hδ : δ ≤ (1 - rate L d) / 2)
    (w : L → F) {c c' : L → F} (hc : c ∈ RS L d) (hc' : c' ∈ RS L d)
    (h1 : relDist w c ≤ δ) (h2 : relDist w c' ≤ δ) : c = c' :=
  RS_unique_decoding δ (half_one_sub_rate_lt d hδ) w hc hc' h1 h2

end RS

/-! ### Even–odd split of words (equation (2.3) and Lemma 2.22) -/

section Split

variable {L : Subgroup Fˣ}

/-- The value `ξ ∈ F` of a point `ξ ∈ L`. -/
abbrev xv (ξ : L) : F := ((ξ : Fˣ) : F)

/-- Equation (even-odd): `w_e(ξ²) = (w(ξ) + w(-ξ))/2`, defined via a chosen square root. -/
noncomputable def evenW (w : L → F) : sqDom L → F :=
  fun η => (w (sqrtPt η) + w (negPt (sqrtPt η))) / 2

/-- Equation (even-odd): `w_o(ξ²) = (w(ξ) - w(-ξ))/(2ξ)`, defined via a chosen square root. -/
noncomputable def oddW (w : L → F) : sqDom L → F :=
  fun η => (w (sqrtPt η) - w (negPt (sqrtPt η))) / (2 * xv (sqrtPt η))

/-- Lemma 2.22(1) (well defined): `w_e(ξ²) = (w(ξ) + w(-ξ))/2` for *every* `ξ ∈ L`. -/
theorem evenW_sqPt (hL : (-1 : Fˣ) ∈ L) (w : L → F) (ξ : L) :
    evenW w (sqPt ξ) = (w ξ + w (negPt ξ)) / 2 := by
  unfold evenW
  rcases (sqPt_eq_iff hL (sqrtPt (sqPt ξ)) ξ).1 (sqPt_sqrtPt _) with h | h
  · rw [h]
  · rw [h, negPt_negPt hL, add_comm]

/-- Lemma 2.22(1) (well defined): `w_o(ξ²) = (w(ξ) - w(-ξ))/(2ξ)` for *every* `ξ ∈ L`. -/
theorem oddW_sqPt (hL : (-1 : Fˣ) ∈ L) (w : L → F) (ξ : L) :
    oddW w (sqPt ξ) = (w ξ - w (negPt ξ)) / (2 * xv ξ) := by
  unfold oddW
  rcases (sqPt_eq_iff hL (sqrtPt (sqPt ξ)) ξ).1 (sqPt_sqrtPt _) with h | h
  · rw [h]
  · rw [h, negPt_negPt hL, xv, val_negPt hL, mul_neg, div_neg, ← neg_div, neg_sub]

/-- Lemma 2.22(1): `w ↦ w_e` is `F`-linear. -/
noncomputable def evenLin (L : Subgroup Fˣ) : (L → F) →ₗ[F] (sqDom L → F) where
  toFun := evenW
  map_add' w w' := by funext η; simp [evenW]; ring
  map_smul' a w := by funext η; simp [evenW]; ring

/-- Lemma 2.22(1): `w ↦ w_o` is `F`-linear. -/
noncomputable def oddLin (L : Subgroup Fˣ) : (L → F) →ₗ[F] (sqDom L → F) where
  toFun := oddW
  map_add' w w' := by funext η; simp [oddW]; ring
  map_smul' a w := by funext η; simp [oddW]; ring

@[simp] lemma evenLin_apply (w : L → F) : evenLin L w = evenW w := rfl
@[simp] lemma oddLin_apply (w : L → F) : oddLin L w = oddW w := rfl

/-- Lemma 2.22(2) (locality): `w_e(η)` depends only on `w` on the fibre over `η`. -/
theorem evenW_congr {w w' : L → F} {η : sqDom L} (h : ∀ ξ ∈ fibre η, w ξ = w' ξ) :
    evenW w η = evenW w' η := by
  unfold evenW
  rw [h _ (sqrtPt_mem_fibre η), h _ (negPt_mem_fibre (sqrtPt_mem_fibre η))]

/-- Lemma 2.22(2) (locality): `w_o(η)` depends only on `w` on the fibre over `η`. -/
theorem oddW_congr {w w' : L → F} {η : sqDom L} (h : ∀ ξ ∈ fibre η, w ξ = w' ξ) :
    oddW w η = oddW w' η := by
  unfold oddW
  rw [h _ (sqrtPt_mem_fibre η), h _ (negPt_mem_fibre (sqrtPt_mem_fibre η))]

/-- Lemma 2.22(3): `w(ξ) = w_e(ξ²) + ξ w_o(ξ²)`. -/
theorem eval_pos_split (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (w : L → F) (ξ : L) :
    w ξ = evenW w (sqPt ξ) + xv ξ * oddW w (sqPt ξ) := by
  rw [evenW_sqPt hL, oddW_sqPt hL]
  have hξ : xv ξ ≠ 0 := Units.ne_zero _
  field_simp
  ring

/-- Lemma 2.22(3): `w(-ξ) = w_e(ξ²) - ξ w_o(ξ²)`. -/
theorem eval_neg_split (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (w : L → F) (ξ : L) :
    w (negPt ξ) = evenW w (sqPt ξ) - xv ξ * oddW w (sqPt ξ) := by
  rw [evenW_sqPt hL, oddW_sqPt hL]
  have hξ : xv ξ ≠ 0 := Units.ne_zero _
  field_simp
  ring

/-- Lemma 2.22(3): `w` vanishes on the fibre over `η` iff `w_e(η) = w_o(η) = 0`. -/
theorem vanish_fibre_iff (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (w : L → F) (η : sqDom L) :
    (∀ ξ ∈ fibre η, w ξ = 0) ↔ evenW w η = 0 ∧ oddW w η = 0 := by
  constructor
  · intro h
    have e1 := evenW_congr (w' := 0) (η := η) (by simpa using h)
    have e2 := oddW_congr (w' := 0) (η := η) (by simpa using h)
    simp [evenW, oddW] at e1 e2
    exact ⟨by simp [evenW, e1], by simp [oddW, e2]⟩
  · rintro ⟨he, ho⟩ ξ hξ
    rw [mem_fibre] at hξ
    subst hξ
    rw [eval_pos_split hL h2 w ξ, he, ho, mul_zero, add_zero]

/-- Evaluating the even–odd decomposition `P(X) = P_e(X²) + X P_o(X²)`. -/
lemma eval_even_odd (P : F[X]) (x : F) :
    P.eval x = (evenPart P).eval (x ^ 2) + x * (oddPart P).eval (x ^ 2) := by
  conv_lhs => rw [even_odd_decomp P]
  simp [expand_eval]

/-- Lemma 2.22(4): `ev_L(P)_e = ev_{L²}(P_e)` (for every polynomial `P`). -/
theorem evenW_ev (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (P : F[X]) :
    evenW (ev L P) = ev (sqDom L) (evenPart P) := by
  funext η
  rw [← sqPt_sqrtPt η, evenW_sqPt hL]
  simp only [ev, val_negPt hL, val_sqPt]
  rw [eval_even_odd P, eval_even_odd P (-_)]
  field_simp
  ring

/-- Lemma 2.22(4): `ev_L(P)_o = ev_{L²}(P_o)` (for every polynomial `P`). -/
theorem oddW_ev (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (P : F[X]) :
    oddW (ev L P) = ev (sqDom L) (oddPart P) := by
  funext η
  rw [← sqPt_sqrtPt η, oddW_sqPt hL]
  have hξ : xv (sqrtPt η) ≠ 0 := Units.ne_zero _
  simp only [ev, val_negPt hL, val_sqPt]
  rw [eval_even_odd P, eval_even_odd P (-_)]
  simp only [xv] at hξ ⊢
  field_simp
  ring

/-- Lemma 2.3(1), degree part: `P ∈ F[X]_{<2d} ⇒ P_e ∈ F[X]_{<d}`. -/
lemma evenPart_mem_degreeLT {d : ℕ} {P : F[X]} (hP : P ∈ degreeLT F (2 * d)) :
    evenPart P ∈ degreeLT F d := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at *
  intro m hm
  rw [coeff_evenPart]; exact hP _ (by omega)

/-- Lemma 2.3(1), degree part: `P ∈ F[X]_{<2d} ⇒ P_o ∈ F[X]_{<d}`. -/
lemma oddPart_mem_degreeLT {d : ℕ} {P : F[X]} (hP : P ∈ degreeLT F (2 * d)) :
    oddPart P ∈ degreeLT F d := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at *
  intro m hm
  rw [coeff_oddPart]; exact hP _ (by omega)

/-- Lemma 2.22(4): the even and odd parts of a codeword of `RS[L,2d]` lie in `RS[L²,d]`. -/
theorem evenW_oddW_mem_RS (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) {d : ℕ} {c : L → F}
    (hc : c ∈ RS L (2 * d)) : evenW c ∈ RS (sqDom L) d ∧ oddW c ∈ RS (sqDom L) d := by
  obtain ⟨P, hP, rfl⟩ := mem_RS.1 hc
  rw [evenW_ev hL h2, oddW_ev hL h2]
  exact ⟨ev_mem_RS (evenPart_mem_degreeLT hP), ev_mem_RS (oddPart_mem_degreeLT hP)⟩

end Split

end KBFold
