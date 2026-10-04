/-
SumFRI/SkipRBR.lean
Theorem 6.32(2): round-by-round knowledge soundness of `Π_eval^J` (committed levels `J`), with the
doomed set of `Π_eval` pulled back through the augmentation (§6.8): a partial transcript of
`Π_eval^J` is doomed iff its augmentation is doomed (Definition 6.17).

* `augWord`, `augPT`: the augmentation of a partial transcript (the omitted words are the
  classical folds of the preceding augmented words, computed from the transcript);
* `augWord_updR`: the inserted words before round `j+1` do not depend on `θ_{j+1}`;
* items 1–3 of Theorem 6.20 for `Π_eval^J`: `crbr_round_one_J`, `crbr_round_J`, `crbr_final_J`,
  with the errors of Theorem 6.20.
-/
import SumFRI.RBRGeneric
import SumFRI.Skip

set_option autoImplicit false

open Polynomial

namespace SumFRI

open KBFold

variable {F : Type*} [Field F]

section Aug

variable {L : Subgroup Fˣ} (J : Finset ℕ) (w0 : L → F)

/-- The augmented words of a partial transcript of `Π_eval^J`: `w_0`, the committed words
`τ.w j` for `j ∈ J`, and the classical folds of the preceding augmented word otherwise. -/
noncomputable def augWord (τ : PTrans F L) : (j : ℕ) → lv L j → F
  | 0 => w0
  | k + 1 => if k + 1 ∈ J then τ.w (k + 1) else cwfold (τ.r k) (augWord τ k)

/-- The augmentation of a partial transcript (the map `aug` of §6.8). -/
noncomputable def augPT (τ : PTrans F L) : PTrans F L := ⟨τ.s, augWord J w0 τ, τ.r⟩

lemma Wd_augPT (τ : PTrans F L) : Wd w0 (augPT J w0 τ) = augWord J w0 τ := by
  funext j; cases j <;> rfl

/-- The augmented words up to level `j` do not depend on the challenge `θ_{j+1}`. -/
lemma augWord_updR (τ : PTrans F L) (j : ℕ) (a : F) :
    ∀ k ≤ j, augWord J w0 (τ.updR j a) k = augWord J w0 τ k
  | 0, _ => rfl
  | k + 1, hk => by
      have ih := augWord_updR τ j a k (by omega)
      simp only [augWord]
      rw [ih]
      simp only [PTrans.updR, Function.update_of_ne (show k ≠ j by omega)]

variable {m : ℕ} {ℓ : ℕ} {zp : ℕ → F} {zs : Fin m → F} {v : F} {δ : ℚ}

/-- `aug(τ_{j+1})` and `aug(τ_j)` with the challenge `θ_{j+1}` agree on everything that
Definition 6.17 reads at round `j+1`. -/
theorem cNotDoomed_augPT_updR (τ : PTrans F L) (j : ℕ) (a : F) :
    cNotDoomed ℓ w0 zp zs v δ (augPT J w0 (τ.updR j a)) (j + 1) ↔
      cNotDoomed ℓ w0 zp zs v δ ((augPT J w0 τ).updR j a) (j + 1) := by
  apply cNotDoomed_congr
  intro k hk
  refine ⟨rfl, rfl, ?_⟩
  show augWord J w0 (τ.updR j a) k = augWord J w0 τ k
  exact augWord_updR J w0 τ j a k (by omega)

end Aug

/-! ### Transfer of acceptance -/

/-- Two provers with the same round polynomials, the same final table and the same verifier
words up to level `ℓ` are accepted on the same transcripts. -/
lemma accepts_of_W_eq {L : Subgroup Fˣ} {m : ℕ} (P Q : SumProver F L m) (ℓ : ℕ) (w0 : L → F)
    (zp : ℕ → F) (zs : Fin m → F) (v : F) (θ : ℕ → F) {κ : ℕ} (ξ : Fin κ → L)
    (hs : P.s = Q.s) (hg : P.g = Q.g) (hW : ∀ j ≤ ℓ, P.W ℓ w0 θ j = Q.W ℓ w0 θ j) :
    P.Accepts ℓ w0 zp zs v θ ξ → Q.Accepts ℓ w0 zp zs v θ ξ := by
  rintro ⟨hR, hC, hQ⟩
  have hvv : P.vv v θ = Q.vv v θ := by
    funext i
    cases i with
    | zero => rfl
    | succ i => simp only [SumProver.vv, hs]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have := hR i hi
    rw [hs, hvv] at this
    exact this
  · have : P.vv v θ ℓ = cpoly (P.g θ) zs := hC
    rw [hvv, hg] at this
    exact this
  · intro t
    refine ⟨?_, ?_⟩
    · intro j hj
      have := (hQ t).1 j hj
      simp only [SumProver.Chk] at this ⊢
      rw [hW j (by omega), hW (j + 1) hj] at this
      exact this
    · intro h0
      have := (hQ t).2 h0
      rw [hg] at this
      exact this

section Final

variable {L : Subgroup Fˣ} {m : ℕ} (J : Finset ℕ) (w0 : L → F)

lemma augW_eq_augWord (τ : PTrans F L) (g : Table F m) (ℓ : ℕ) :
    ∀ j < ℓ, (cproverOf τ g).augW ℓ J w0 τ.r j = augWord J w0 τ j
  | 0, _ => rfl
  | k + 1, hk => by
      have ih := augW_eq_augWord τ g ℓ k (by omega)
      simp only [SumProver.augW, augWord, if_neg (show k + 1 ≠ ℓ by omega)]
      rw [ih]
      all_goals (split_ifs <;> rfl)

/-- The verifier words of the augmented prover of Lemma 5.6 are those of the augmented
transcript. -/
lemma aug_W_eq_cprover (τ : PTrans F L) (g : Table F m) (ℓ : ℕ) :
    ∀ j ≤ ℓ, ((cproverOf τ g).aug ℓ J w0).W ℓ w0 τ.r j =
      (cproverOf (augPT J w0 τ) g).W ℓ w0 τ.r j := by
  intro j hj
  rw [SumProver.aug_W_eq _ ℓ J w0 τ.r j hj]
  rcases j with _ | k
  · rfl
  · by_cases h : k + 1 = ℓ
    · subst h
      simp [SumProver.augW, SumProver.W, cproverOf]
    · rw [augW_eq_augWord J w0 τ g ℓ (k + 1) (by omega)]
      simp only [SumProver.W, if_neg h]
      rfl

end Final

/-! ### Theorem 6.32(2): items 1–3 of Theorem 6.20 for `Π_eval^J` -/

section Theorem

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {w0 : L → F} {zp : ℕ → F} {zs : Fin m → F} {v : F}
  {δ : ℚ} (J : Finset ℕ)

/-- **Theorem 6.32(2), round 1.** If the output of `cExt` is not a witness, then for every
round-1 message, the augmented `τ_1` is not doomed with probability at most `(M_1 + 1)/|F|`. -/
theorem crbr_round_one_J [Fintype F] [DecidableEq F] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (hnw : ¬ cIsWitness ℓ w0 zp zs v δ (cExt ℓ w0 δ)) (τ : PTrans F L)
    (hdeg : (τ.s 0).natDegree ≤ 1) :
    prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ (augPT J w0 (τ.updR 0 a)) 1) ≤
      ((Nat.card (lv L 1) : ℚ) + 1) / Fintype.card F := by
  have h := crbr_round_one hL hℓ hδ0 hδ hnw (augPT J w0 τ) hdeg
  calc prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ (augPT J w0 (τ.updR 0 a)) 1)
      = prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ ((augPT J w0 τ).updR 0 a) 1) := by
        congr 1; funext a; exact propext (cNotDoomed_augPT_updR J w0 τ 0 a)
    _ ≤ _ := h

/-- **Theorem 6.32(2), round `j+1`, `1 ≤ j < ℓ`.** If the augmentation of `τ_j` is doomed, then
for every round-`(j+1)` message, the augmentation of `τ_{j+1}` is not doomed with probability at
most `(M_{j+1} + 1)/|F|`. -/
theorem crbr_round_J [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (τ : PTrans F L) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j < ℓ) (hdoom : cDoomed ℓ w0 zp zs v δ (augPT J w0 τ) j)
    (hdeg : (τ.s j).natDegree ≤ 1) :
    prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ (augPT J w0 (τ.updR j a)) (j + 1)) ≤
      ((Nat.card (lv L (j + 1)) : ℚ) + 1) / Fintype.card F := by
  have h := crbr_round hL hδ0 hδ (augPT J w0 τ) hj1 hj hdoom hdeg
  calc prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ (augPT J w0 (τ.updR j a)) (j + 1))
      = prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ ((augPT J w0 τ).updR j a) (j + 1)) := by
        congr 1; funext a; exact propext (cNotDoomed_augPT_updR J w0 τ j a)
    _ ≤ _ := h

/-- **Theorem 6.32(2), round `ℓ+1`.** If the augmentation of `τ_ℓ` is doomed, then for every
final message `g`, the verifier of `Π_eval^J` accepts with probability at most `(1-δ)^κ`. -/
theorem crbr_final_J [Fintype L] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (τ : PTrans F L)
    (hdoom : cDoomed ℓ w0 zp zs v δ (augPT J w0 τ) ℓ) (g : Table F m) (κ : ℕ) :
    prob (fun ξ : Fin κ → L => (cproverOf τ g).AcceptsJ ℓ J w0 zp zs v τ.r ξ) ≤ (1 - δ) ^ κ := by
  refine (prob_mono (fun ξ h => ?_)).trans (crbr_final hL hℓ hδ (augPT J w0 τ) hdoom g κ)
  have h1 := caccepts_aug (cproverOf τ g) ℓ J w0 zp zs v τ.r ξ h
  exact accepts_of_W_eq ((cproverOf τ g).aug ℓ J w0) (cproverOf (augPT J w0 τ) g) ℓ w0 zp zs v
    τ.r ξ rfl rfl (aug_W_eq_cprover J w0 τ g ℓ) h1

end Theorem

end SumFRI
