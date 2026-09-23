/-
KBFold/Kernel.lean
Formalisation of §4 (Boolean-kernel basis) and the polynomial part of §5
(even–odd split, kernel fold, fold dictionary) of the paper.

Conventions: bit `k : Fin n` of the Lean development is bit `k+1` of the paper,
so `K_b(X) = ∏_{k<n} (X^{2^k} + b_k)`.
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import KBFold.Multilinear

open Polynomial Finset

namespace KBFold

variable {F : Type*} [Field F]

/-- Definition 4.1: `K_y(X) = ∏_k (X^{2^k} + y_k)`. -/
noncomputable def kernel {n : ℕ} (y : Fin n → F) : F[X] :=
  ∏ k : Fin n, (X ^ (2 ^ (k : ℕ)) + C (y k))

/-- The Boolean kernel polynomial `K_b`. -/
noncomputable def kernelB {n : ℕ} (b : Fin n → Bool) : F[X] := kernel (pt b)

/-- The polynomial with kernel coordinates `λ`: `U = ∑_b λ(b) K_b`. -/
noncomputable def ofCoords {n : ℕ} (lam : Table F n) : F[X] :=
  ∑ b, C (lam b) * kernelB b

/-! ### Lemma 4.5 (recursion), first-bit form -/

lemma expand_X_pow_two_pow (k : ℕ) :
    expand F 2 (X ^ (2 ^ k) : F[X]) = X ^ (2 ^ (k + 1)) := by
  rw [map_pow, expand_X, ← pow_mul, pow_succ, mul_comm]

/-- `K_{(y₀,y)}(X) = (X + y₀) · K_y(X²)`. -/
theorem kernel_cons {n : ℕ} (y0 : F) (y : Fin n → F) :
    kernel (Fin.cons y0 y : Fin (n+1) → F) = (X + C y0) * expand F 2 (kernel y) := by
  unfold kernel
  rw [Fin.prod_univ_succ, map_prod]
  congr 1
  · simp
  · refine Finset.prod_congr rfl (fun k _ => ?_)
    simp [map_add, expand_C, expand_X_pow_two_pow]

/-! ### Even and odd parts (Lemma 2.3(1)) -/

/-- Even part: `coeff (evenPart U) i = coeff U (2i)`. -/
noncomputable def evenPart (U : F[X]) : F[X] := contract 2 U

/-- Odd part: `coeff (oddPart U) i = coeff U (2i+1)`. -/
noncomputable def oddPart (U : F[X]) : F[X] := contract 2 (divX U)

lemma coeff_evenPart (U : F[X]) (i : ℕ) : (evenPart U).coeff i = U.coeff (2 * i) := by
  simp [evenPart, coeff_contract two_ne_zero, mul_comm]

lemma coeff_oddPart (U : F[X]) (i : ℕ) : (oddPart U).coeff i = U.coeff (2 * i + 1) := by
  simp [oddPart, coeff_contract two_ne_zero, coeff_divX, mul_comm]

lemma coeff_X_mul_gen (p : F[X]) (m : ℕ) :
    (X * p).coeff m = if m = 0 then 0 else p.coeff (m - 1) := by
  cases m with
  | zero => simp
  | succ k => simp [coeff_X_mul]

/-- `U(X) = U_e(X²) + X U_o(X²)`. -/
theorem even_odd_decomp (U : F[X]) :
    U = expand F 2 (evenPart U) + X * expand F 2 (oddPart U) := by
  ext m
  rw [coeff_add, coeff_X_mul_gen, coeff_expand two_pos]
  rcases Nat.even_or_odd m with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [if_pos ⟨i, by ring⟩, show (i + i) / 2 = i by omega, coeff_evenPart,
      show 2 * i = i + i by ring]
    split_ifs with h
    · simp
    · rw [coeff_expand two_pos, if_neg (by omega)]; simp
  · rw [if_neg (by omega), if_neg (by omega), coeff_expand two_pos,
      if_pos (by omega), show (2 * i + 1 - 1) / 2 = i by omega, coeff_oddPart]
    simp

/-- Uniqueness of the even–odd split. -/
theorem even_odd_unique (P Q : F[X]) :
    evenPart (expand F 2 P + X * expand F 2 Q) = P ∧
    oddPart (expand F 2 P + X * expand F 2 Q) = Q := by
  constructor
  · ext i
    rw [coeff_evenPart, coeff_add, coeff_X_mul_gen, coeff_expand two_pos,
      if_pos ⟨i, rfl⟩, show 2 * i / 2 = i by omega]
    split_ifs with h
    · simp
    · rw [coeff_expand two_pos, if_neg (by omega)]; simp
  · ext i
    rw [coeff_oddPart, coeff_add, coeff_X_mul_gen, coeff_expand two_pos,
      if_neg (by omega), if_neg (by omega), coeff_expand two_pos,
      if_pos (by omega), show (2 * i + 1 - 1) / 2 = i by omega]
    simp

/-! ### Proposition 5.1 (even–odd split in kernel coordinates) -/

theorem kernelB_cons_false {n : ℕ} (b' : Fin n → Bool) :
    (kernelB (Fin.cons false b' : Fin (n+1) → Bool) : F[X]) = X * expand F 2 (kernelB b') := by
  have : (pt (Fin.cons false b' : Fin (n+1) → Bool) : Fin (n+1) → F) = Fin.cons 0 (pt b') := by
    funext k; refine Fin.cases ?_ ?_ k <;> simp [pt, bval]
  rw [kernelB, this, kernel_cons]; simp [kernelB]

theorem kernelB_cons_true {n : ℕ} (b' : Fin n → Bool) :
    (kernelB (Fin.cons true b' : Fin (n+1) → Bool) : F[X])
      = expand F 2 (kernelB b') + X * expand F 2 (kernelB b') := by
  have : (pt (Fin.cons true b' : Fin (n+1) → Bool) : Fin (n+1) → F) = Fin.cons 1 (pt b') := by
    funext k; refine Fin.cases ?_ ?_ k <;> simp [pt, bval]
  rw [kernelB, this, kernel_cons]; simp [kernelB]; ring

/-- Proposition 5.1: `U = U_e(X²) + X U_o(X²)` with
`U_e = ∑ λ(1,b') K_{b'}` and `U_o = ∑ (λ(0,b') + λ(1,b')) K_{b'}`. -/
theorem ofCoords_split {n : ℕ} (lam : Table F (n+1)) :
    ofCoords lam = expand F 2 (ofCoords (fun b' => lam (Fin.cons true b')))
      + X * expand F 2 (ofCoords (fun b' => lam (Fin.cons false b') + lam (Fin.cons true b'))) := by
  unfold ofCoords
  rw [sum_cons_bool]
  simp only [kernelB_cons_false, kernelB_cons_true, map_sum, map_mul, map_add, expand_C,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  ring

theorem evenPart_ofCoords {n : ℕ} (lam : Table F (n+1)) :
    evenPart (ofCoords lam) = ofCoords (fun b' => lam (Fin.cons true b')) := by
  rw [ofCoords_split]; exact (even_odd_unique _ _).1

theorem oddPart_ofCoords {n : ℕ} (lam : Table F (n+1)) :
    oddPart (ofCoords lam) = ofCoords (fun b' => lam (Fin.cons false b') + lam (Fin.cons true b')) := by
  rw [ofCoords_split]; exact (even_odd_unique _ _).2

/-! ### Definition 5.2 and Theorem 5.3 (fold dictionary) -/

/-- `pfold_r(U) = (2r-1) U_e + (1-r) U_o`. -/
noncomputable def pfold (r : F) (U : F[X]) : F[X] :=
  C (2 * r - 1) * evenPart U + C (1 - r) * oddPart U

lemma ofCoords_add {n : ℕ} (f g : Table F n) :
    ofCoords (f + g) = ofCoords f + ofCoords g := by
  unfold ofCoords; simp [C_add, add_mul, Finset.sum_add_distrib]

lemma ofCoords_smul {n : ℕ} (a : F) (f : Table F n) :
    ofCoords (fun b => a * f b) = C a * ofCoords f := by
  unfold ofCoords; simp [C_mul, Finset.mul_sum, mul_assoc]

/-- Theorem 5.3 (fold dictionary): the kernel coordinates of `pfold_r(U)`
are the restriction `res_r(λ)`. -/
theorem fold_dictionary {n : ℕ} (r : F) (lam : Table F (n+1)) :
    pfold r (ofCoords lam) = ofCoords (res r lam) := by
  unfold pfold
  rw [evenPart_ofCoords, oddPart_ofCoords, ← ofCoords_smul, ← ofCoords_smul, ← ofCoords_add]
  congr 1
  funext b'
  simp only [res, Pi.add_apply]
  ring


/-! ### Corollary 5.4 (iterated folding evaluates the multilinear extension) -/

/-- Successive folds `pfold_{r_1}, …, pfold_{r_j}`. -/
noncomputable def pfoldList : List F → F[X] → F[X]
  | [], U => U
  | r :: rs, U => pfoldList rs (pfold r U)

lemma ofCoords_zero_vars (lam : Table F 0) : ofCoords lam = C (lam Fin.elim0) := by
  unfold ofCoords kernelB kernel
  rw [Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  exact congrArg (fun b => C (lam b)) (Subsingleton.elim _ _)

/-- Corollary 5.4: folding `n` times with challenges `r` gives the constant `λ~(r)`. -/
theorem pfoldList_ofCoords : ∀ {n : ℕ} (lam : Table F n) (r : Fin n → F),
    pfoldList (List.ofFn r) (ofCoords lam) = C (mle lam r)
  | 0, lam, r => by
      rw [List.ofFn_zero, pfoldList, ofCoords_zero_vars]
      congr 1
      unfold mle eqv
      rw [Fintype.sum_unique]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      exact congrArg lam (Subsingleton.elim _ _)
  | n+1, lam, r => by
      rw [List.ofFn_succ, pfoldList, fold_dictionary, pfoldList_ofCoords (res (r 0) lam)]
      congr 1
      rw [mle_res]
      congr 1
      exact Fin.cons_self_tail r

/-! ### Degree bound and Theorem 4.8 (basis) -/

lemma natDegree_kernelB : ∀ {n : ℕ} (b : Fin n → Bool),
    (kernelB b : F[X]).natDegree ≤ 2 ^ n - 1
  | 0, b => by simp [kernelB, kernel]
  | n+1, b => by
      obtain ⟨β, b', rfl⟩ : ∃ β b', b = (Fin.cons β b' : Fin (n+1) → Bool) :=
        ⟨b 0, Fin.tail b, (Fin.cons_self_tail b).symm⟩
      have ih : (kernelB b' : F[X]).natDegree ≤ 2 ^ n - 1 := natDegree_kernelB b'
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      cases β
      · rw [kernelB_cons_false]
        calc (X * expand F 2 (kernelB b')).natDegree
            ≤ X.natDegree + (expand F 2 (kernelB b')).natDegree := natDegree_mul_le
          _ ≤ 1 + 2 * (2 ^ n - 1) := by
              gcongr
              · exact natDegree_X_le
              · rw [natDegree_expand]; omega
          _ ≤ 2 ^ (n+1) - 1 := by rw [pow_succ]; omega
      · rw [kernelB_cons_true]
        calc (expand F 2 (kernelB b') + X * expand F 2 (kernelB b')).natDegree
            ≤ max (expand F 2 (kernelB b')).natDegree
                (X * expand F 2 (kernelB b')).natDegree := natDegree_add_le _ _
          _ ≤ 2 ^ (n+1) - 1 := by
              apply max_le
              · rw [natDegree_expand]; rw [pow_succ]; omega
              · calc (X * expand F 2 (kernelB b')).natDegree
                    ≤ X.natDegree + (expand F 2 (kernelB b')).natDegree := natDegree_mul_le
                  _ ≤ 1 + 2 * (2 ^ n - 1) := by
                      gcongr
                      · exact natDegree_X_le
                      · rw [natDegree_expand]; omega
                  _ ≤ 2 ^ (n+1) - 1 := by rw [pow_succ]; omega

lemma ofCoords_mem_degreeLT {n : ℕ} (lam : Table F n) : ofCoords lam ∈ degreeLT F (2 ^ n) := by
  unfold ofCoords
  refine Submodule.sum_mem _ (fun b _ => ?_)
  rw [mem_degreeLT]
  calc (C (lam b) * kernelB b).degree ≤ (kernelB b : F[X]).degree := by
        rw [← smul_eq_C_mul]; exact degree_smul_le _ _
    _ ≤ ((2 ^ n - 1 : ℕ) : WithBot ℕ) := degree_le_of_natDegree_le (natDegree_kernelB b)
    _ < (2 ^ n : ℕ) := by
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        exact_mod_cast (by omega : 2 ^ n - 1 < 2 ^ n)

/-- Injectivity of `λ ↦ ∑ λ(b) K_b` (linear independence of the Boolean kernel family). -/
theorem ofCoords_eq_zero : ∀ {n : ℕ} (lam : Table F n), ofCoords lam = 0 → lam = 0
  | 0, lam, h => by
      rw [ofCoords_zero_vars, C_eq_zero] at h
      funext b; rw [Subsingleton.elim b Fin.elim0]; simpa using h
  | n+1, lam, h => by
      have h1 := evenPart_ofCoords lam
      have h2 := oddPart_ofCoords lam
      rw [h] at h1 h2
      have e1 : (fun b' => lam (Fin.cons true b')) = 0 :=
        ofCoords_eq_zero _ (by rw [← h1]; simp [evenPart, contract])
      have e2 : (fun b' => lam (Fin.cons false b') + lam (Fin.cons true b')) = 0 :=
        ofCoords_eq_zero _ (by rw [← h2]; simp [oddPart, contract])
      funext b
      rw [← Fin.cons_self_tail b]
      have t1 := congrFun e1 (Fin.tail b)
      have t2 := congrFun e2 (Fin.tail b)
      simp only [Pi.zero_apply] at t1 t2
      cases b 0
      · simpa [t1] using t2
      · simpa using t1


/-- The linear map `λ ↦ ∑_b λ(b) K_b` into `F[X]_{<2^n}`. -/
noncomputable def ofCoordsLin (n : ℕ) : Table F n →ₗ[F] degreeLT F (2 ^ n) where
  toFun lam := ⟨ofCoords lam, ofCoords_mem_degreeLT lam⟩
  map_add' f g := by ext1; exact ofCoords_add f g
  map_smul' a f := by
    ext1
    simp only [RingHom.id_apply, SetLike.val_smul, smul_eq_C_mul]
    exact ofCoords_smul a f

/-- Theorem 4.8(3): the Boolean kernel family is a basis of `F[X]_{<2^n}`. -/
theorem ofCoordsLin_bijective (n : ℕ) : Function.Bijective (ofCoordsLin (F := F) n) := by
  have inj : Function.Injective (ofCoordsLin (F := F) n) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro lam h
    exact ofCoords_eq_zero lam (congrArg Subtype.val h)
  refine ⟨inj, ?_⟩
  have hdim : Module.finrank F (Table F n) = Module.finrank F (degreeLT F (2 ^ n)) := by
    rw [Module.finrank_fintype_fun_eq_card, (degreeLTEquiv F (2 ^ n)).finrank_eq,
      Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_bool, Fintype.card_fin]
  haveI : FiniteDimensional F (degreeLT F (2 ^ n)) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv F (2 ^ n)).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp inj

/-- Every polynomial of degree `< 2^n` has unique kernel coordinates (Definition 4.10). -/
theorem exists_unique_coords {n : ℕ} (U : F[X]) (hU : U ∈ degreeLT F (2 ^ n)) :
    ∃! lam : Table F n, ofCoords lam = U := by
  obtain ⟨lam, hlam⟩ := (ofCoordsLin_bijective (F := F) n).2 ⟨U, hU⟩
  refine ⟨lam, congrArg Subtype.val hlam, fun mu hmu => ?_⟩
  apply (ofCoordsLin_bijective (F := F) n).1
  ext1
  exact hmu.trans (congrArg Subtype.val hlam).symm

end KBFold
