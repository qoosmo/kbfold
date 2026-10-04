/-
SumFRI/Monomial.lean
Formalisation of §4 of the Sum-FRI paper (the restriction dictionary), on top of the KBFold
library:
* Definition 3.9  `cpoly`      the coefficient polynomial `P_f = ∑_a f(a) m_a`;
* Definition 4.1  `vpoly`      the coefficient encoding `V_f = ∑_a f(a) X^a`;
* Lemma 4.2       `vpoly_eval`, `vpoly_eval_one`   Kronecker substitution, `V_f(1) = ∑ f`;
* Definition 4.3  `cres`, `cresSeq`               coefficient restriction;
* Lemma 4.4       `cpoly_cres`, `cpoly_cresSeq`   it evaluates the first variables of `P_f`;
* Theorem 4.6     `cfold_vpoly`, `cfoldSeq_vpoly`, `cfoldSeq_vpoly_full`   restriction dictionary;
* Lemma 4.8(4)    `cwfold_ev`                     word fold = polynomial fold on `L²`;
* Lemma 4.11      `hround_eq`, `hround_one`, `affine_agree`   the round polynomial.

Conventions are those of KBFold (see `KBFold/Multilinear.lean`): a table with `n` variables is
`(Fin n → Bool) → F`, bit `0` is the least significant one, and `b = b₁ + 2b'` is
`Fin.cons b₁ b'`.  The classical fold `cfold`, `cwfold`, `cfoldSeq` and `shiftSeq`, `catPt` are
those of `KBFold/WordFold.lean`.
-/
import KBFold.WordFold
import KBFold.Mobius

open Polynomial Finset

namespace SumFRI

open KBFold

variable {F : Type*} [Field F]

/-! ### The coefficient polynomial and coefficient restriction -/

/-- Definition 3.9: the coefficient polynomial `P_f(x) = ∑_a f(a) m_a(x)`. -/
def cpoly {n : ℕ} (f : Table F n) (x : Fin n → F) : F := ∑ a, f a * mono a x

lemma mono_cons_false {n : ℕ} (a : Fin n → Bool) (x0 : F) (x : Fin n → F) :
    mono (Fin.cons false a : Fin (n + 1) → Bool) (Fin.cons x0 x) = mono a x := by
  unfold mono
  rw [Fin.prod_univ_succ]
  simp

lemma mono_cons_true {n : ℕ} (a : Fin n → Bool) (x0 : F) (x : Fin n → F) :
    mono (Fin.cons true a : Fin (n + 1) → Bool) (Fin.cons x0 x) = x0 * mono a x := by
  unfold mono
  rw [Fin.prod_univ_succ]
  simp

/-- Definition 4.3: `cres_θ(f)(b') = f(2b') + θ f(2b'+1)`. -/
def cres {n : ℕ} (θ : F) (f : Table F (n + 1)) : Table F n :=
  fun b' => f (Fin.cons false b') + θ * f (Fin.cons true b')

/-- Lemma 4.4(1): `P_{cres_θ(f)}(y) = P_f(θ, y)`. -/
theorem cpoly_cres {n : ℕ} (θ : F) (f : Table F (n + 1)) (y : Fin n → F) :
    cpoly (cres θ f) y = cpoly f (Fin.cons θ y) := by
  unfold cpoly cres
  rw [sum_cons_bool]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  rw [mono_cons_false, mono_cons_true]
  ring

/-- Definition 4.3: iterated coefficient restriction at `θ 0, θ 1, …` of a table with `m + j`
variables. -/
def cresSeq : (j : ℕ) → {m : ℕ} → (ℕ → F) → Table F (m + j) → Table F m
  | 0, _, _, f => f
  | j + 1, _, θ, f => cresSeq j (shiftSeq θ) (cres (θ 0) f)

/-- Lemma 4.4(2): `P_{cres_{θ≤j}(f)}(y) = P_f(θ_1, …, θ_j, y)`. -/
theorem cpoly_cresSeq : ∀ (j : ℕ) {m : ℕ} (θ : ℕ → F) (f : Table F (m + j)) (y : Fin m → F),
    cpoly (cresSeq j θ f) y = cpoly f (catPt j θ y)
  | 0, _, _, _, _ => rfl
  | j + 1, _, θ, f, y => by
      simp only [cresSeq, catPt]
      rw [cpoly_cresSeq j (shiftSeq θ) (cres (θ 0) f) y, cpoly_cres]

/-- `P_f(1, …, 1) = ∑_a f(a)` (equation (2)). -/
theorem cpoly_one {n : ℕ} (f : Table F n) : cpoly f (fun _ => 1) = ∑ a, f a := by
  simp [cpoly, mono]

/-! ### The coefficient encoding -/

/-- Definition 4.1: `V_f = ∑_a f(a) X^a`. -/
noncomputable def vpoly {n : ℕ} (f : Table F n) : F[X] := ∑ a, C (f a) * X ^ bitsToNat a

/-- Linearity of `f ↦ V_f`, in the form used by the fold. -/
theorem vpoly_lin {n : ℕ} (f g : Table F n) (θ : F) :
    vpoly (fun b => f b + θ * g b) = vpoly f + C θ * vpoly g := by
  unfold vpoly
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [map_add, map_mul]
  ring

/-- Lemma 4.2: `V_f(ζ) = P_f(ζ, ζ², …, ζ^{2^{n-1}})`. -/
theorem vpoly_eval {n : ℕ} (f : Table F n) (ζ : F) :
    (vpoly f).eval ζ = cpoly f (fun k => ζ ^ (2 ^ (k : ℕ))) := by
  unfold vpoly cpoly
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  unfold mono bitsToNat
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  split_ifs <;> simp

/-- Lemma 4.2: `V_f(1) = ∑_a f(a)`. -/
theorem vpoly_eval_one {n : ℕ} (f : Table F n) : (vpoly f).eval 1 = ∑ a, f a := by
  rw [vpoly_eval]
  simpa using cpoly_one f

/-- The even--odd split of `V_f` along the first bit: `V_f = V_{f_e}(X²) + X V_{f_o}(X²)`. -/
theorem vpoly_split {n : ℕ} (f : Table F (n + 1)) :
    vpoly f = expand F 2 (vpoly (fun b' => f (Fin.cons false b')))
      + X * expand F 2 (vpoly (fun b' => f (Fin.cons true b'))) := by
  unfold vpoly
  rw [sum_cons_bool]
  simp only [bitsToNat_cons, map_sum, map_mul, expand_C, map_pow, expand_X, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add,
    pow_add, pow_mul, pow_one]
  ring

theorem evenPart_vpoly {n : ℕ} (f : Table F (n + 1)) :
    evenPart (vpoly f) = vpoly (fun b' => f (Fin.cons false b')) := by
  rw [vpoly_split]; exact (even_odd_unique _ _).1

theorem oddPart_vpoly {n : ℕ} (f : Table F (n + 1)) :
    oddPart (vpoly f) = vpoly (fun b' => f (Fin.cons true b')) := by
  rw [vpoly_split]; exact (even_odd_unique _ _).2

/-- `V_f` of a table with no variable is the constant `P_f()`. -/
theorem vpoly_zero (f : Table F 0) : vpoly f = C (cpoly f Fin.elim0) := by
  simp [vpoly, cpoly, mono, bitsToNat]

/-! ### Theorem 4.6 (restriction dictionary) -/

/-- Theorem 4.6: `cfold_θ(V_f) = V_{cres_θ(f)}`. -/
theorem cfold_vpoly {n : ℕ} (θ : F) (f : Table F (n + 1)) :
    cfold θ (vpoly f) = vpoly (cres θ f) := by
  unfold cfold cres
  rw [evenPart_vpoly, oddPart_vpoly, vpoly_lin]

/-- Theorem 4.6, iterated: `cfold_{θ≤j}(V_f) = V_{cres_{θ≤j}(f)}`. -/
theorem cfoldSeq_vpoly : ∀ (j : ℕ) {m : ℕ} (θ : ℕ → F) (f : Table F (m + j)),
    cfoldSeq j θ (vpoly f) = vpoly (cresSeq j θ f)
  | 0, _, _, _ => rfl
  | j + 1, _, θ, f => by
      simp only [cfoldSeq, cresSeq]
      rw [cfold_vpoly, cfoldSeq_vpoly j]

/-- Theorem 4.6, `j = n`: `n` classical folds of `V_f` give the constant `P_f(θ_1, …, θ_n)`. -/
theorem cfoldSeq_vpoly_full (n : ℕ) (θ : ℕ → F) (f : Table F (0 + n)) :
    cfoldSeq n θ (vpoly f) = C (cpoly f (catPt n θ Fin.elim0)) := by
  rw [cfoldSeq_vpoly, vpoly_zero, cpoly_cresSeq]

/-! ### Lemma 4.8 (the classical word fold) -/

section Words

variable {L : Subgroup Fˣ}

/-- Lemma 4.8(4): `cfold_θ(ev_L U) = ev_{L²}(cfold_θ U)`. -/
theorem cwfold_ev (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (θ : F) (U : F[X]) :
    cwfold θ (ev L U) = ev (sqDom L) (cfold θ U) := by
  unfold cwfold cfold
  rw [evenW_ev hL h2, oddW_ev hL h2]
  funext η
  simp [ev]

end Words

/-! ### Definition 4.10 and Lemma 4.11 (the round polynomial) -/

/-- The constant term `P_{g_e}(y)` of the honest round polynomial. -/
def rnd0 {n : ℕ} (g : Table F (n + 1)) (y : Fin n → F) : F :=
  cpoly (fun b' => g (Fin.cons false b')) y

/-- The linear coefficient `P_{g_o}(y)` of the honest round polynomial. -/
def rnd1 {n : ℕ} (g : Table F (n + 1)) (y : Fin n → F) : F :=
  cpoly (fun b' => g (Fin.cons true b')) y

/-- Lemma 4.11(1): `h_{g,y}(t) = P_g(t, y) = P_{cres_t(g)}(y)`. -/
theorem hround_eq {n : ℕ} (g : Table F (n + 1)) (y : Fin n → F) (t : F) :
    rnd0 g y + t * rnd1 g y = cpoly g (Fin.cons t y) := by
  rw [← cpoly_cres]
  unfold rnd0 rnd1 cpoly cres
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  ring

/-- Lemma 4.11(2): for `y = (1, …, 1)` the coefficients are `U_e(1)` and `U_o(1)`, `U = V_g`. -/
theorem hround_one {n : ℕ} (g : Table F (n + 1)) :
    rnd0 g (fun _ => 1) = (evenPart (vpoly g)).eval 1 ∧
      rnd1 g (fun _ => 1) = (oddPart (vpoly g)).eval 1 := by
  rw [evenPart_vpoly, oddPart_vpoly, vpoly_eval_one, vpoly_eval_one]
  exact ⟨cpoly_one _, cpoly_one _⟩

/-- Lemma 4.11(3): two distinct affine polynomials `a₀ + T a₁` and `b₀ + T b₁` agree on at most
one point. -/
theorem affine_agree {a0 a1 b0 b1 : F} (h : a0 ≠ b0 ∨ a1 ≠ b1) :
    {θ : F | a0 + θ * a1 = b0 + θ * b1}.Subsingleton := by
  intro x hx y hy
  simp only [Set.mem_setOf_eq] at hx hy
  by_contra hne
  have h1 : a1 = b1 := by
    have hm : (x - y) * (a1 - b1) = 0 := by linear_combination hx - hy
    rcases mul_eq_zero.1 hm with h' | h'
    · exact absurd (sub_eq_zero.1 h') hne
    · exact sub_eq_zero.1 h'
  have h0 : a0 = b0 := by
    rw [h1] at hx
    linear_combination hx
  rcases h with h | h
  · exact h h0
  · exact h h1

end SumFRI
