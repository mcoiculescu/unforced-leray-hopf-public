import UnforcedLeray.Short.PartIIIb.Concrete.YoungBlocks
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Fpm

/-!
# Block setup facts (source 4376-4411)

NOTE (audit): the original target omitted the reflexivity law `𝒰(t,t) = id`
(`YoungLaws.refl`, source 4338-4350); without it the statement is false
(take `Uev = 0`). It is added as the hypothesis `hrefl`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

theorem block_setup_facts (pk : YoungPkg) (lam κ : ℂ) (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t)
    (hrefl : ∀ s, pk.Uev s s = ContinuousLinearMap.id ℂ pk.X)
    (hg : GramLaw pk) (C : ℝ) (hC : ∀ j : Bool, ‖pk.q j t‖ ≤ C ∧ ‖pk.ell j t‖ ≤ C) :
    (∀ (x : pk.X) (j : Bool) (s : ℝ), 0 ≤ s →
        pk.ell j s (pk.Uev s t x) = Fpm j lam κ ν s t * ampN pk lam κ ν t x j s) ∧
    (∀ (x : pk.X) (s : ℝ), 0 ≤ s →
        ‖Pc pk s (pk.Uev s t x)‖ = ‖Fpm true lam κ ν s t‖ * cmpN pk lam κ ν t x s) ∧
    (∀ j i : Bool, ampN pk lam κ ν t (pk.q j t) i t = if i = j then 1 else 0) ∧
    (∀ j : Bool, cmpN pk lam κ ν t (pk.q j t) t = 0) ∧
    (∀ (y : pk.X) (i : Bool), ampN pk lam κ ν t (Pc pk t y) i t = 0) ∧
    (∀ y : pk.X, cmpN pk lam κ ν t (Pc pk t y) t = ‖Pc pk t y‖ ∧
      ‖Pc pk t y‖ ≤ (1 + 2 * C ^ 2) * ‖y‖) := by
  have hF1 : ∀ j : Bool, Fpm j lam κ ν t t = 1 := (fpm_facts ν hν lam κ t t ht ht).1
  have hPc : ∀ y : pk.X, Pc pk t y =
      y - (pk.ell true t y • pk.q true t + pk.ell false t y • pk.q false t) := by
    intro y
    simp [Pc, Fintype.sum_bool]
  have hPq : ∀ j : Bool, Pc pk t (pk.q j t) = 0 := by
    intro j
    rw [hPc, hg t true j, hg t false j]
    cases j <;> simp
  have hellP : ∀ (y : pk.X) (i : Bool), pk.ell i t (Pc pk t y) = 0 := by
    intro y i
    rw [hPc]
    simp only [map_sub, map_add, map_smul, smul_eq_mul, hg t i true, hg t i false]
    cases i <;> simp
  have hPP : ∀ y : pk.X, Pc pk t (Pc pk t y) = Pc pk t y := by
    intro y
    rw [hPc (Pc pk t y), hellP y true, hellP y false]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x j s hs
    have hne := (fpm_facts ν hν lam κ s t hs ht).2.1 j
    unfold ampN
    field_simp
  · intro x s hs
    have hne := (fpm_facts ν hν lam κ s t hs ht).2.1 true
    have : ‖Fpm true lam κ ν s t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    unfold cmpN
    field_simp
  · intro j i
    unfold ampN
    rw [hrefl t]
    simp only [ContinuousLinearMap.id_apply, hF1 i, hg t i j, div_one]
  · intro j
    unfold cmpN
    rw [hrefl t]
    simp [hPq j]
  · intro y i
    unfold ampN
    rw [hrefl t]
    simp [hellP y i]
  · intro y
    refine ⟨?_, ?_⟩
    · unfold cmpN
      rw [hrefl t]
      have hne := (fpm_facts ν hν lam κ t t ht ht).2.1 true
      have : ‖Fpm true lam κ ν t t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
      simp only [ContinuousLinearMap.id_apply, hF1 true, norm_one, div_one, hPP y]
    · have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC true).1
      rw [hPc y]
      have hb : ∀ j : Bool, ‖(pk.ell j t y) • pk.q j t‖ ≤ C ^ 2 * ‖y‖ := by
        intro j
        rw [norm_smul]
        calc ‖pk.ell j t y‖ * ‖pk.q j t‖ ≤ (C * ‖y‖) * C := by
              apply mul_le_mul _ (hC j).1 (norm_nonneg _) (by positivity)
              exact ((pk.ell j t).le_opNorm y).trans
                (mul_le_mul_of_nonneg_right (hC j).2 (norm_nonneg _))
          _ = C ^ 2 * ‖y‖ := by ring
      calc ‖y - (pk.ell true t y • pk.q true t + pk.ell false t y • pk.q false t)‖
          ≤ ‖y‖ + ‖pk.ell true t y • pk.q true t + pk.ell false t y • pk.q false t‖ :=
            norm_sub_le _ _
        _ ≤ ‖y‖ + (C ^ 2 * ‖y‖ + C ^ 2 * ‖y‖) := by
            gcongr
            exact (norm_add_le _ _).trans (add_le_add (hb true) (hb false))
        _ = (1 + 2 * C ^ 2) * ‖y‖ := by ring

end ConcreteYF

end UnforcedLeray.Short.PartIIIb
