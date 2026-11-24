import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_4

/-!
# `PartIII-a:T21/2/7/2/1/2/1/4`, task `sortPerm`: sorting permutation

Proves `SortPerm` (defined in `Sub/PartIII-a_T21_2_7_2_1_2_1_4.lean`, SP 3060-3073, calculus only).
Induction on the word: the first letter `a` of `i` either is the age letter (then it is moved to the
end, by `Fin.cycleRange (Fin.last m)`) or is spatial (then it stays first).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem spSpatWordCons {m : ℕ} (a : Fin 3) (t : Fin m → Fin 3) :
    spatWord (Fin.cons a t : Fin (m + 1) → Fin 3) =
      if h : a = 0 then spatWord t else a.pred h :: spatWord t := by
  unfold spatWord
  rw [List.ofFn_succ]
  by_cases h : a = 0 <;> simp [h]

theorem spAgeCountCons {m : ℕ} (a : Fin 3) (t : Fin m → Fin 3) :
    ageCount (Fin.cons a t : Fin (m + 1) → Fin 3) = (if a = 0 then 1 else 0) + ageCount t := by
  unfold ageCount
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp

theorem spLengthAdd : ∀ (n : ℕ) (i : Fin n → Fin 3), (spatWord i).length + ageCount i = n
  | 0, i => by simp [spatWord, ageCount]
  | m + 1, i => by
    obtain ⟨a, t, rfl⟩ : ∃ a t, i = Fin.cons a t := ⟨i 0, Fin.tail i, (Fin.cons_self_tail i).symm⟩
    have ih := spLengthAdd m t
    rw [spSpatWordCons, spAgeCountCons]
    by_cases h : a = 0 <;> simp [h] <;> omega

theorem spSortAux : ∀ (n : ℕ) (i : Fin n → Fin 3),
    ∃ σ : Equiv.Perm (Fin n), ∀ k, stDir (i (σ k)) = sortedVec (spatWord i) n k
  | 0, _ => ⟨Equiv.refl _, fun k => k.elim0⟩
  | m + 1, i => by
    obtain ⟨a, t, rfl⟩ : ∃ a t, i = Fin.cons a t := ⟨i 0, Fin.tail i, (Fin.cons_self_tail i).symm⟩
    obtain ⟨σ', hσ'⟩ := spSortAux m t
    have hlen := spLengthAdd m t
    rw [spSpatWordCons]
    set τ : Equiv.Perm (Fin (m + 1)) := Equiv.Perm.decomposeFin.symm (0, σ') with hτ
    by_cases ha : a = 0
    · subst ha
      rw [dif_pos rfl]
      refine ⟨τ * Fin.cycleRange (Fin.last m), fun k => ?_⟩
      induction k using Fin.lastCases with
      | last =>
        have hlt : ¬ ((Fin.last m : Fin (m + 1)) : ℕ) < (spatWord t).length := by
          rw [Fin.val_last]; omega
        rw [Equiv.Perm.mul_apply, Fin.cycleRange_self, hτ,
          Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cons_zero]
        simp only [sortedVec, dif_neg hlt]
      | cast x =>
        have hc : Fin.cycleRange (Fin.last m) (Fin.castSucc x) = x.succ := by
          apply Fin.ext
          rw [Fin.coe_cycleRange_of_lt (Fin.castSucc_lt_last x)]
          simp
        rw [Equiv.Perm.mul_apply, hc, hτ, Equiv.Perm.decomposeFin_symm_apply_succ,
          Equiv.swap_self, Equiv.refl_apply, Fin.cons_succ, hσ' x]
        simp [sortedVec]
    · rw [dif_neg ha]
      refine ⟨τ, fun k => ?_⟩
      induction k using Fin.cases with
      | zero =>
        rw [hτ, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cons_zero]
        simp [sortedVec, Fin.succ_pred]
      | succ x =>
        rw [hτ, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
          Fin.cons_succ, hσ' x]
        simp [sortedVec]

theorem sortPerm : UnforcedLeray.Short.IIIa.SortPerm := by
  intro n i
  exact ⟨spLengthAdd n i, spSortAux n i⟩

end UnforcedLeray.Short.IIIa
