import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Defs

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4/1/3` : Gaussian envelope of one lattice term

Source `the November 2 reference manuscript`
lines 4978 and 5063-5071.  `|psiT| ≤ 4|M|(1+|y|)⁴e^{-|y|²/9}`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiTValBound : PsiTValBound := by
  refine ⟨4, by norm_num, ?_⟩
  intro ν s hν hs hνs M y
  have ha1 := pdc_ageA_ge_one hν.le hs
  have hexp := pdc_exp_le hν.le hs hνs y
  have hepos : 0 < Real.exp (-(sq2 y) / (2 * ageA ν s)) := Real.exp_pos _
  have hw0 : 0 < (ageA ν s ^ 4)⁻¹ := by positivity
  have hw1 : (ageA ν s ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha1)
  have hQ := pdc_qM_le M y
  have hF := pdc_frob_nonneg M
  have hn := norm_nonneg y
  have hG : 0 < Real.exp (-(‖y‖ ^ 2) / 9) := Real.exp_pos _
  have hn2 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 4 := by
    nlinarith [pow_nonneg hn 3, pow_nonneg hn 4, sq_nonneg ‖y‖]
  have h1 : (ageA ν s ^ 4)⁻¹ * |qM M y| ≤ 4 * frob M * ‖y‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hw1 (abs_nonneg (qM M y))
    linarith
  have h2 : Real.exp (-(sq2 y) / (2 * ageA ν s)) * ((ageA ν s ^ 4)⁻¹ * |qM M y|)
      ≤ Real.exp (-(‖y‖ ^ 2) / 9) * (4 * frob M * ‖y‖ ^ 2) :=
    mul_le_mul hexp h1 (mul_nonneg hw0.le (abs_nonneg _)) hG.le
  have h3 : ‖y‖ ^ 2 * Real.exp (-(‖y‖ ^ 2) / 9) ≤ (1 + ‖y‖) ^ 4 * Real.exp (-(‖y‖ ^ 2) / 9) :=
    mul_le_mul_of_nonneg_right hn2 hG.le
  unfold psiT genvT
  rw [abs_mul, abs_mul, abs_of_pos hepos, abs_of_pos hw0]
  calc Real.exp (-(sq2 y) / (2 * ageA ν s)) * ((ageA ν s ^ 4)⁻¹ * |qM M y|)
      ≤ Real.exp (-(‖y‖ ^ 2) / 9) * (4 * frob M * ‖y‖ ^ 2) := h2
    _ = 4 * frob M * (‖y‖ ^ 2 * Real.exp (-(‖y‖ ^ 2) / 9)) := by ring
    _ ≤ 4 * frob M * ((1 + ‖y‖) ^ 4 * Real.exp (-(‖y‖ ^ 2) / 9)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 4 * frob M * ((1 + ‖y‖) ^ 4 * Real.exp (-(‖y‖ ^ 2) / 9)) := rfl

end UnforcedLeray.Short.PartIIIb.Concrete
