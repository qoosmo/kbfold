/-
KBFold/Multilinear.lean
Formalisation of §2.3 of the paper "The Boolean-Kernel Basis":
equality polynomial, multilinear extension (as an evaluation formula),
restriction of the first variable, naturality.

Conventions (see the Lean companion notes):
* A point of the Boolean hypercube `B_n` is a bit vector `b : Fin n → Bool`;
  bit `b 0` is the paper's `b_1` (least significant bit).
* A table over a commutative ring `A` with `n` variables is a function
  `Table A n := (Fin n → Bool) → A`.
* Splitting off the first bit, the paper's `b = b_1 + 2 b'`, is `Fin.cons b₁ b'`.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

open Finset

namespace KBFold

variable {A : Type*} [CommRing A]

/-- The ring element `0` or `1` of a bit. -/
def bval (β : Bool) : A := if β then 1 else 0

/-- The embedding `B_n ⊆ A^n` of §2.1. -/
def pt {n : ℕ} (b : Fin n → Bool) : Fin n → A := fun k => bval (b k)

/-- `eq₁(y,z) = yz + (1-y)(1-z)` (Definition 2.4). -/
def eq1 (y z : A) : A := y * z + (1 - y) * (1 - z)

/-- `eq(y,z) = ∏ₖ eq₁(y_k, z_k)` (Definition 2.4). -/
def eqv {n : ℕ} (y z : Fin n → A) : A := ∏ k, eq1 (y k) (z k)

/-- Tables with `n` variables over `A` (Proposition 2.6). -/
abbrev Table (A : Type*) (n : ℕ) := (Fin n → Bool) → A

/-- Evaluation of the multilinear extension: `f̃(x) = ∑_b f(b) eq(b,x)` (Proposition 2.6). -/
def mle {n : ℕ} (f : Table A n) (x : Fin n → A) : A := ∑ b, f b * eqv (pt b) x

/-! ### Lemma 2.5 (equality polynomial) -/

lemma eq1_comm (y z : A) : eq1 y z = eq1 z y := by
  unfold eq1; ring

lemma eqv_comm {n : ℕ} (y z : Fin n → A) : eqv y z = eqv z y := by
  unfold eqv; exact Finset.prod_congr rfl (fun k _ => eq1_comm _ _)

/-- Lemma 2.5(4). -/
lemma eq1_false (r : A) : eq1 (bval false) r = 1 - r := by simp [eq1, bval]

/-- Lemma 2.5(4). -/
lemma eq1_true (r : A) : eq1 (bval true) r = r := by simp [eq1, bval]

lemma eq1_bool [Nontrivial A] (β γ : Bool) :
    eq1 (bval β : A) (bval γ) = if β = γ then 1 else 0 := by
  cases β <;> cases γ <;> simp [eq1, bval]

/-- Lemma 2.5(1): `eq(b,c) = [b = c]` on the hypercube. -/
lemma eqv_pt [Nontrivial A] {n : ℕ} (b c : Fin n → Bool) :
    eqv (pt b : Fin n → A) (pt c) = if b = c then 1 else 0 := by
  unfold eqv pt
  simp_rw [eq1_bool]
  split_ifs with h
  · subst h; simp
  · obtain ⟨k, hk⟩ : ∃ k, b k ≠ c k := by
      by_contra hne; push_neg at hne; exact h (funext hne)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

/-- Lemma 2.5(3), first variable: `eq((y₀,y),(z₀,z)) = eq₁(y₀,z₀) eq(y,z)`. -/
lemma eqv_cons {n : ℕ} (y0 z0 : A) (y z : Fin n → A) :
    eqv (Fin.cons y0 y : Fin (n+1) → A) (Fin.cons z0 z) = eq1 y0 z0 * eqv y z := by
  unfold eqv
  rw [Fin.prod_univ_succ]
  simp

/-- Lemma 2.5(3): `eq((x,x'),(z,z')) = eq(x,z) eq(x',z')`. -/
lemma eqv_append {j m : ℕ} (x z : Fin j → A) (x' z' : Fin m → A) :
    eqv (Fin.append x x') (Fin.append z z') = eqv x z * eqv x' z' := by
  unfold eqv
  rw [Fin.prod_univ_add]
  simp

/-! ### Proposition 2.6 (interpolation) -/

/-- The multilinear extension interpolates its table. -/
lemma mle_pt [Nontrivial A] {n : ℕ} (f : Table A n) (c : Fin n → Bool) :
    mle f (pt c) = f c := by
  unfold mle
  simp_rw [eqv_pt, mul_ite, mul_one, mul_zero]
  simp

/-- `mle` is linear in the table. -/
lemma mle_add {n : ℕ} (f g : Table A n) (x : Fin n → A) :
    mle (f + g) x = mle f x + mle g x := by
  unfold mle; simp [add_mul, Finset.sum_add_distrib]

lemma mle_smul {n : ℕ} (a : A) (f : Table A n) (x : Fin n → A) :
    mle (fun b => a * f b) x = a * mle f x := by
  unfold mle; rw [Finset.mul_sum]; simp [mul_assoc]

/-! ### Corollary 2.7 (multilinear extension of the equality table) -/

lemma sum_bool_eq1 (y z : A) :
    ∑ β : Bool, eq1 (bval β) z * eq1 (bval β) y = eq1 y z := by
  simp [eq1, bval]; ring

/-- `∑_b eq(b,z) eq(b,x) = eq(x,z)`: the multilinear extension of `b ↦ eq(b,z)`
evaluated at `x` is `eq(x,z)`. -/
lemma mle_eqTable {n : ℕ} (z x : Fin n → A) :
    mle (fun b => eqv (pt b) z) x = eqv x z := by
  unfold mle eqv
  simp_rw [← Finset.prod_mul_distrib]
  have h : ∏ k : Fin n, ∑ β : Bool, eq1 (bval β : A) (z k) * eq1 (bval β) (x k)
      = ∑ b : Fin n → Bool, ∏ k, eq1 (bval (b k) : A) (z k) * eq1 (bval (b k)) (x k) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp only [pt]
  rw [← h]
  exact Finset.prod_congr rfl (fun k _ => sum_bool_eq1 (x k) (z k))

/-! ### Definition 2.10 and Lemma 2.11 (restriction) -/

/-- Restriction of the first variable at `r` (Definition 2.10):
`res_r(f)(b') = (1-r) f(0,b') + r f(1,b')`. -/
def res {n : ℕ} (r : A) (f : Table A (n+1)) : Table A n :=
  fun b' => (1 - r) * f (Fin.cons false b') + r * f (Fin.cons true b')

/-- Splitting a sum over bit vectors of length `n+1` along the first bit. -/
lemma sum_cons_bool {n : ℕ} (g : (Fin (n+1) → Bool) → A) :
    ∑ b, g b = ∑ b' : Fin n → Bool, (g (Fin.cons false b') + g (Fin.cons true b')) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp [Fin.consEquiv, Finset.sum_add_distrib, add_comm]

/-- Lemma 2.11(1): `res_r(f)~(y) = f~(r, y)`, for all `y ∈ A^n`. -/
theorem mle_res {n : ℕ} (r : A) (f : Table A (n+1)) (y : Fin n → A) :
    mle (res r f) y = mle f (Fin.cons r y) := by
  unfold mle res
  rw [sum_cons_bool]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  have h0 : (pt (Fin.cons false b' : Fin (n+1) → Bool) : Fin (n+1) → A)
      = Fin.cons (bval false) (pt b') := by
    funext k; refine Fin.cases ?_ ?_ k <;> simp [pt]
  have h1 : (pt (Fin.cons true b' : Fin (n+1) → Bool) : Fin (n+1) → A)
      = Fin.cons (bval true) (pt b') := by
    funext k; refine Fin.cases ?_ ?_ k <;> simp [pt]
  rw [h0, h1, eqv_cons, eqv_cons, eq1_false, eq1_true]
  ring

/-- Lemma 2.11(2), pointwise form: the restricted table is a value of `f~`. -/
theorem res_eq_mle [Nontrivial A] {n : ℕ} (r : A) (f : Table A (n+1)) (b : Fin n → Bool) :
    res r f b = mle f (Fin.cons r (pt b)) := by
  rw [← mle_res, mle_pt]

/-! ### Lemma 2.12 (naturality) -/

section Naturality
variable {B : Type*} [CommRing B] (φ : A →+* B)

lemma map_bval (β : Bool) : φ (bval β) = bval β := by cases β <;> simp [bval]

lemma map_eqv {n : ℕ} (y z : Fin n → A) : φ (eqv y z) = eqv (φ ∘ y) (φ ∘ z) := by
  simp [eqv, eq1, map_prod]

/-- Lemma 2.12: `φ(f~(x)) = (φ ∘ f)~(φ ∘ x)`. -/
theorem map_mle {n : ℕ} (f : Table A n) (x : Fin n → A) :
    φ (mle f x) = mle (φ ∘ f) (φ ∘ x) := by
  unfold mle
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_mul, map_eqv]
  congr 2
  funext k; simp [pt, map_bval]

/-- Lemma 2.12: `φ ∘ res_r(f) = res_{φ r}(φ ∘ f)`. -/
theorem map_res {n : ℕ} (r : A) (f : Table A (n+1)) :
    φ ∘ res r f = res (φ r) (φ ∘ f) := by
  funext b; simp [res]

end Naturality

end KBFold
