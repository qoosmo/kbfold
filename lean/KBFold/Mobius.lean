/-
KBFold/Mobius.lean
Formalisation of the Kronecker/Möbius parts of the paper:
* §2: Lemma 2.9 (table form ↔ coefficient form, Möbius inversion), with Definition 2.8;
* §4: Lemma 4.3 (coefficient rule), Corollary 4.4 (Boolean coefficients),
  Definition 4.6 (Kronecker products), Lemma 4.7 (mixed-product rule, first statement and
  `I^{⊗n} = I`), Theorem 4.8(1)–(2) (`K_n = C^{⊗n}`, inverse `(C^{-1})^{⊗n}`),
  Corollary 4.11 (explicit transforms; the operation counts are not formalised).

Conventions: an index `a ∈ [0, N-1]` is a bit vector `a : Fin n → Bool` (Lean bit `k` is the
paper's bit `k+1`); the integer it denotes is `bitsToNat a = ∑_k a_k 2^k`.
Matrices are indexed by `Bool` (2×2) or by `Fin n → Bool` (N×N).
-/
import Mathlib.Data.Matrix.Mul
import KBFold.LowDegree

open Polynomial Finset

namespace KBFold

/-! ### Bits, submasks, complements -/

/-- The integer `a = ∑_k a_k 2^{k}` with bit vector `a` (§2.1). -/
def bitsToNat {n : ℕ} (a : Fin n → Bool) : ℕ := ∑ k : Fin n, if a k then 2 ^ (k : ℕ) else 0

lemma bitsToNat_cons {n : ℕ} (β : Bool) (a : Fin n → Bool) :
    bitsToNat (Fin.cons β a : Fin (n + 1) → Bool) = (if β then 1 else 0) + 2 * bitsToNat a := by
  simp only [bitsToNat, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
    Fin.val_succ, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs <;> ring

lemma bitsToNat_lt : ∀ {n : ℕ} (a : Fin n → Bool), bitsToNat a < 2 ^ n
  | 0, a => by simp [bitsToNat]
  | n + 1, a => by
      rw [← Fin.cons_self_tail a, bitsToNat_cons, pow_succ]
      have := bitsToNat_lt (Fin.tail a)
      split_ifs <;> omega

lemma bitsToNat_injective : ∀ {n : ℕ}, Function.Injective (bitsToNat : (Fin n → Bool) → ℕ)
  | 0, a, b, _ => Subsingleton.elim a b
  | n + 1, a, b, h => by
      rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, bitsToNat_cons, bitsToNat_cons] at h
      have h0 : a 0 = b 0 := by
        cases ha : a 0 <;> cases hb : b 0
        · rfl
        · rw [ha, hb] at h; simp at h; omega
        · rw [ha, hb] at h; simp at h; omega
        · rfl
      have ht : Fin.tail a = Fin.tail b := by
        apply bitsToNat_injective; rw [h0] at h; omega
      rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, h0, ht]

/-- §2.1: `b ↦ (b_1, …, b_n)` is a bijection `[0, N-1] → B_n`. -/
theorem bitsToNat_bijective (n : ℕ) :
    Function.Bijective (fun a : Fin n → Bool => (⟨bitsToNat a, bitsToNat_lt a⟩ : Fin (2 ^ n))) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b h => bitsToNat_injective (congrArg Fin.val h), ?_⟩
  simp

/-- `c ⊆ b` (submask, §2.1): `c_k ≤ b_k` for all `k`. -/
def IsSubmask {n : ℕ} (c b : Fin n → Bool) : Prop := ∀ k, c k = true → b k = true

instance {n : ℕ} (c b : Fin n → Bool) : Decidable (IsSubmask c b) := by
  unfold IsSubmask; infer_instance

/-- The complement `b̄ = (N-1) - b`, bitwise. -/
def bcompl {n : ℕ} (b : Fin n → Bool) : Fin n → Bool := fun k => !b k

/-! ### Definition 4.6 and Lemma 4.7 (Kronecker products) -/

section Kron

variable {A : Type*} [CommRing A]

/-- Definition 4.6: `(S_1 ⊗ ⋯ ⊗ S_n)[a,b] = ∏_k S_k[a_k, b_k]` (factor `k` acts on bit `k`). -/
def kron {n : ℕ} (S : Fin n → Matrix Bool Bool A) : Matrix (Fin n → Bool) (Fin n → Bool) A :=
  Matrix.of fun a b => ∏ k, S k (a k) (b k)

@[simp] lemma kron_apply {n : ℕ} (S : Fin n → Matrix Bool Bool A) (a b : Fin n → Bool) :
    kron S a b = ∏ k, S k (a k) (b k) := rfl

/-- Expanding a product of sums over `Bool` into a sum over bit vectors. -/
lemma prod_sum_bool {n : ℕ} (g : Fin n → Bool → A) :
    ∏ k, ∑ β : Bool, g k β = ∑ c : Fin n → Bool, ∏ k, g k (c k) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- Lemma 4.7 (mixed-product rule): `(⊗ S_k)(⊗ T_k) = ⊗ (S_k T_k)`. -/
theorem kron_mul {n : ℕ} (S T : Fin n → Matrix Bool Bool A) :
    kron S * kron T = kron (fun k => S k * T k) := by
  ext a b
  simp only [Matrix.mul_apply, kron_apply, ← Finset.prod_mul_distrib]
  exact (prod_sum_bool (fun k β => S k (a k) β * T k β (b k))).symm

/-- Lemma 4.7: `I^{⊗n}` is the identity. -/
theorem kron_one {n : ℕ} : kron (fun _ : Fin n => (1 : Matrix Bool Bool A)) = 1 := by
  ext a b
  simp only [kron_apply, Matrix.one_apply]
  split_ifs with h
  · subst h; simp
  · obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra hne; push_neg at hne; exact h (funext hne)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

/-- Lemma 4.7: `S^{⊗n} T^{⊗n} = (ST)^{⊗n}`. -/
theorem kron_pow_mul {n : ℕ} (S T : Matrix Bool Bool A) :
    kron (fun _ : Fin n => S) * kron (fun _ => T) = kron (fun _ => S * T) :=
  kron_mul _ _

end Kron

/-! ### Lemma 4.3 and Corollary 4.4 (coefficients of kernel polynomials) -/

section Coeff

variable {F : Type*} [Field F]

lemma coeff_expand_two_even (P : F[X]) (m : ℕ) : (expand F 2 P).coeff (2 * m) = P.coeff m := by
  rw [coeff_expand two_pos, if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m two_pos]

lemma coeff_expand_two_odd (P : F[X]) (m : ℕ) : (expand F 2 P).coeff (2 * m + 1) = 0 := by
  rw [coeff_expand two_pos, if_neg (by omega)]

lemma coeff_X_mul_expand_even (P : F[X]) (m : ℕ) : (X * expand F 2 P).coeff (2 * m) = 0 := by
  rcases m with _ | m
  · simp
  · rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, coeff_X_mul, coeff_expand_two_odd]

lemma coeff_X_mul_expand_odd (P : F[X]) (m : ℕ) :
    (X * expand F 2 P).coeff (2 * m + 1) = P.coeff m := by
  rw [coeff_X_mul, coeff_expand_two_even]

/-- Lemma 4.3 (coefficient rule): `[X^a] K_y = ∏_{k : a_k = 0} y_k`. -/
theorem coeff_kernel : ∀ {n : ℕ} (y : Fin n → F) (a : Fin n → Bool),
    (kernel y).coeff (bitsToNat a) = ∏ k, if a k then 1 else y k
  | 0, y, a => by simp [kernel, bitsToNat]
  | n + 1, y, a => by
      rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail a, kernel_cons, bitsToNat_cons,
        Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← coeff_kernel (Fin.tail y) (Fin.tail a), add_mul, coeff_add, coeff_C_mul]
      cases a 0
      · simp only [Bool.false_eq_true, if_false, zero_add]
        rw [coeff_X_mul_expand_even, coeff_expand_two_even, zero_add]
      · simp only [if_true]
        rw [add_comm 1, coeff_X_mul_expand_odd, coeff_expand_two_odd, mul_zero, add_zero, one_mul]

/-- Corollary 4.4 (Boolean coefficients): `[X^a] K_b = 1` if `b̄ ⊆ a`, and `0` otherwise. -/
theorem coeff_kernelB {n : ℕ} (a b : Fin n → Bool) :
    (kernelB b : F[X]).coeff (bitsToNat a) = if IsSubmask (bcompl b) a then 1 else 0 := by
  rw [kernelB, coeff_kernel]
  split_ifs with h
  · refine Finset.prod_eq_one (fun k _ => ?_)
    cases ha : a k
    · have hb : b k = true := by
        by_contra hb; have := h k (by simp [bcompl, hb]); rw [ha] at this; exact absurd this (by simp)
      simp [pt, bval, hb]
    · simp
  · obtain ⟨k, hk⟩ : ∃ k, bcompl b k = true ∧ a k ≠ true := by
      by_contra hne; push_neg at hne; exact h hne
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    have hb : b k = false := by simpa [bcompl] using hk.1
    simp [hk.2, pt, bval, hb]

/-! ### Theorem 4.8(1)–(2): `K_n = C^{⊗n}` -/

/-- The matrix `K_n[a,b] = [X^a] K_b` of Theorem 4.8. -/
noncomputable def Kmat (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) F :=
  Matrix.of fun a b => (kernelB b : F[X]).coeff (bitsToNat a)

/-- The 2×2 matrix `C = [[0,1],[1,1]]`: `C[0,β] = β`, `C[1,β] = 1`. -/
def Cmat : Matrix Bool Bool F := Matrix.of fun α β => if α then 1 else bval β

/-- The 2×2 matrix `C^{-1} = [[-1,1],[1,0]]`. -/
def Cinv : Matrix Bool Bool F := Matrix.of fun α β =>
  if α then (if β then 0 else 1) else (if β then 1 else -1)

lemma Cinv_mul_Cmat : (Cinv : Matrix Bool Bool F) * Cmat = 1 := by
  ext α β; cases α <;> cases β <;> simp [Matrix.mul_apply, Cinv, Cmat, bval]

lemma Cmat_mul_Cinv : (Cmat : Matrix Bool Bool F) * Cinv = 1 := by
  ext α β; cases α <;> cases β <;> simp [Matrix.mul_apply, Cinv, Cmat, bval]

/-- Theorem 4.8(1): `K_n = C^{⊗n}`. -/
theorem Kmat_eq_kron (n : ℕ) : (Kmat n : Matrix _ _ F) = kron (fun _ => Cmat) := by
  ext a b
  simp only [Kmat, Matrix.of_apply, kron_apply, kernelB, coeff_kernel, Cmat, pt]

/-- Theorem 4.8(2): `K_n` is invertible with inverse `(C^{-1})^{⊗n}`. -/
theorem Kmat_inv (n : ℕ) :
    kron (fun _ => Cinv) * (Kmat n : Matrix _ _ F) = 1 ∧
      (Kmat n : Matrix _ _ F) * kron (fun _ => Cinv) = 1 := by
  rw [Kmat_eq_kron, kron_mul, kron_mul]
  simp only [Cinv_mul_Cmat, Cmat_mul_Cinv, kron_one, and_self]

/-! ### Corollary 4.11 (explicit transforms) -/

/-- Corollary 4.11 / Definition 4.10: `coef(U) = C^{⊗n} λ`, i.e. the coefficient vector of
`U = ∑ λ(b) K_b` is `K_n λ`. -/
theorem coeff_ofCoords_mulVec {n : ℕ} (lam : Table F n) :
    (fun a => (ofCoords lam).coeff (bitsToNat a)) = (Kmat n).mulVec lam := by
  funext a
  simp only [ofCoords, finset_sum_coeff, coeff_C_mul, Matrix.mulVec, dotProduct, Kmat,
    Matrix.of_apply]
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

/-- Corollary 4.11 (first transform): `[X^a] U = ∑_{b : b̄ ⊆ a} λ(b)`. -/
theorem coeff_ofCoords {n : ℕ} (lam : Table F n) (a : Fin n → Bool) :
    (ofCoords lam).coeff (bitsToNat a) =
      ∑ b ∈ Finset.univ.filter (fun b => IsSubmask (bcompl b) a), lam b := by
  simp only [ofCoords, finset_sum_coeff, coeff_C_mul, coeff_kernelB, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_filter]

/-- Entries of `(C^{-1})^{⊗n}`: `(C^{-1})^{⊗n}[b,a] = (-1)^{wt(b̄) - wt(a)}` if `a ⊆ b̄`, else `0`. -/
theorem kron_Cinv_apply {n : ℕ} (b a : Fin n → Bool) :
    kron (fun _ : Fin n => (Cinv : Matrix Bool Bool F)) b a =
      if IsSubmask a (bcompl b) then (-1) ^ (wt (bcompl b) - wt a) else 0 := by
  simp only [kron_apply]
  split_ifs with h
  · have hk : ∀ k, (Cinv : Matrix Bool Bool F) (b k) (a k) =
        (-1) ^ ((if bcompl b k then 1 else 0) - (if a k then 1 else 0)) := by
      intro k
      cases hb : b k <;> cases ha : a k <;> simp [Cinv, bcompl, hb]
      exact absurd (h k ha) (by simp [bcompl, hb])
    simp_rw [hk]
    rw [Finset.prod_pow_eq_pow_sum, wt, wt, Finset.sum_tsub_distrib]
    intro k _
    cases ha : a k
    · simp
    · simp [h k ha]
  · obtain ⟨k, hk⟩ : ∃ k, a k = true ∧ bcompl b k ≠ true := by
      by_contra hne; push_neg at hne; exact h hne
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    have hb : b k = true := by simpa [bcompl] using hk.2
    simp [Cinv, hk.1, hb]

/-- Corollary 4.11 (second transform):
`λ(b) = ∑_{a ⊆ b̄} (-1)^{wt(b̄) - wt(a)} [X^a] U` for `U = ∑ λ(b) K_b`. -/
theorem coords_of_coeff {n : ℕ} (lam : Table F n) (b : Fin n → Bool) :
    lam b = ∑ a ∈ Finset.univ.filter (fun a => IsSubmask a (bcompl b)),
      (-1) ^ (wt (bcompl b) - wt a) * (ofCoords lam).coeff (bitsToNat a) := by
  have h := congrArg (fun v => (kron (fun _ => (Cinv : Matrix Bool Bool F))).mulVec v)
    (coeff_ofCoords_mulVec lam)
  simp only [Matrix.mulVec_mulVec, (Kmat_inv n).1, Matrix.one_mulVec] at h
  have h' := congrFun h b
  rw [← h']
  simp only [Matrix.mulVec, dotProduct, kron_Cinv_apply, ite_mul, zero_mul]
  rw [Finset.sum_filter]

end Coeff

/-! ### Definition 2.8 and Lemma 2.9 (table form ↔ coefficient form) -/

section Mobius

variable {A : Type*} [CommRing A]

/-- Definition 2.4: the canonical monomial `m_a(x) = ∏_k x_k^{a_k}`. -/
def mono {n : ℕ} (a : Fin n → Bool) (x : Fin n → A) : A := ∏ k, if a k then x k else 1

/-- `m_a(b) = [a ⊆ b]` on the hypercube. -/
lemma mono_pt [Nontrivial A] {n : ℕ} (a b : Fin n → Bool) :
    mono a (pt b : Fin n → A) = if IsSubmask a b then 1 else 0 := by
  unfold mono
  split_ifs with h
  · refine Finset.prod_eq_one (fun k _ => ?_)
    cases ha : a k
    · simp
    · simp [pt, bval, h k ha]
  · obtain ⟨k, hk⟩ : ∃ k, a k = true ∧ b k ≠ true := by
      by_contra hne; push_neg at hne; exact h hne
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    simp [hk.1, pt, bval, hk.2]

/-- The zeta matrix `Z[b,a] = [a ⊆ b] = ∏_k Z₁[b_k, a_k]`, `Z₁ = [[1,0],[1,1]]`. -/
def Z1 : Matrix Bool Bool A := Matrix.of fun β α => if α then (if β then 1 else 0) else 1

/-- The Möbius matrix factor `Z₁^{-1} = [[1,0],[-1,1]]`. -/
def Z1inv : Matrix Bool Bool A := Matrix.of fun β α => if α then (if β then 1 else 0)
  else (if β then -1 else 1)

lemma Z1inv_mul_Z1 : (Z1inv : Matrix Bool Bool A) * Z1 = 1 := by
  ext α β; cases α <;> cases β <;> simp [Matrix.mul_apply, Z1inv, Z1]

lemma kron_Z1_apply [Nontrivial A] {n : ℕ} (b a : Fin n → Bool) :
    kron (fun _ : Fin n => (Z1 : Matrix Bool Bool A)) b a = if IsSubmask a b then 1 else 0 := by
  rw [← mono_pt]; simp only [kron_apply, mono, Z1, Matrix.of_apply, pt]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  cases a k <;> cases b k <;> simp [bval]

lemma kron_Z1inv_apply {n : ℕ} (a b : Fin n → Bool) :
    kron (fun _ : Fin n => (Z1inv : Matrix Bool Bool A)) a b =
      if IsSubmask b a then (-1) ^ (wt a - wt b) else 0 := by
  simp only [kron_apply]
  split_ifs with h
  · have hk : ∀ k, (Z1inv : Matrix Bool Bool A) (a k) (b k) =
        (-1) ^ ((if a k then 1 else 0) - (if b k then 1 else 0)) := by
      intro k
      cases ha : a k <;> cases hb : b k <;> simp [Z1inv]
      exact absurd (h k hb) (by simp [ha])
    simp_rw [hk]
    rw [Finset.prod_pow_eq_pow_sum, wt, wt, Finset.sum_tsub_distrib]
    intro k _
    cases hb : b k
    · simp
    · simp [h k hb]
  · obtain ⟨k, hk⟩ : ∃ k, b k = true ∧ a k ≠ true := by
      by_contra hne; push_neg at hne; exact h hne
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    have ha : a k = false := by simpa using hk.2
    simp [Z1inv, hk.1, ha]

/-- Möbius transform `α_a = ∑_{b ⊆ a} (-1)^{wt(a) - wt(b)} f(b)` (Lemma 2.9). -/
def mobius {n : ℕ} (f : Table A n) : Table A n :=
  fun a => ∑ b ∈ Finset.univ.filter (fun b => IsSubmask b a), (-1) ^ (wt a - wt b) * f b

lemma mobius_eq_mulVec {n : ℕ} (f : Table A n) :
    mobius f = (kron (fun _ : Fin n => (Z1inv : Matrix Bool Bool A))).mulVec f := by
  funext a
  simp only [mobius, Matrix.mulVec, dotProduct, kron_Z1inv_apply, ite_mul, zero_mul]
  rw [Finset.sum_filter]

/-- Definition 2.8 / Lemma 2.9 (existence of the coefficient form): the multilinear extension
is `f~ = ∑_a α_a m_a` with `α = mobius f`. -/
theorem mle_eq_sum_mono {n : ℕ} (f : Table A n) (x : Fin n → A) :
    mle f x = ∑ a, mobius f a * mono a x := by
  rw [mobius_eq_mulVec]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold mle
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have : eqv (pt b) x = ∑ a, kron (fun _ : Fin n => (Z1inv : Matrix Bool Bool A)) a b * mono a x := by
    simp only [kron_apply, mono, ← Finset.prod_mul_distrib]
    rw [← prod_sum_bool (fun k β => (Z1inv : Matrix Bool Bool A) β (b k) * (if β then x k else 1))]
    unfold eqv
    refine Finset.prod_congr rfl (fun k _ => ?_)
    cases hb : b k
    · simp [Z1inv, eq1, pt, bval, hb]; ring
    · simp [Z1inv, eq1, pt, bval, hb]
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- Lemma 2.9: if `f~ = ∑_a α_a m_a` (Definition 2.8), then
`f(b) = ∑_{a ⊆ b} α_a` and `α_a = ∑_{b ⊆ a} (-1)^{wt(a) - wt(b)} f(b)`. -/
theorem table_coeff_form [Nontrivial A] {n : ℕ} (f : Table A n) (α : Table A n)
    (hα : ∀ x, mle f x = ∑ a, α a * mono a x) :
    (∀ b, f b = ∑ a ∈ Finset.univ.filter (fun a => IsSubmask a b), α a) ∧
      (∀ a, α a = ∑ b ∈ Finset.univ.filter (fun b => IsSubmask b a),
        (-1) ^ (wt a - wt b) * f b) := by
  have h1 : ∀ b, f b = ∑ a ∈ Finset.univ.filter (fun a => IsSubmask a b), α a := by
    intro b
    rw [← mle_pt f b, hα, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [mono_pt]; split_ifs <;> simp
  refine ⟨h1, fun a => ?_⟩
  have hf : f = (kron (fun _ : Fin n => (Z1 : Matrix Bool Bool A))).mulVec α := by
    funext b
    rw [h1 b]
    simp only [Matrix.mulVec, dotProduct, kron_Z1_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_filter]
  have hm : mobius f = α := by
    rw [mobius_eq_mulVec, hf, Matrix.mulVec_mulVec, kron_mul]
    simp only [Z1inv_mul_Z1, kron_one, Matrix.one_mulVec]
  exact (congrFun hm a).symm

end Mobius

end KBFold
