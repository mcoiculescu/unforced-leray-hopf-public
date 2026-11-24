import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Defs

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4/1/4` : Gaussian envelope of the `η`-derivative

Source `the November 2 reference manuscript`
lines 4978, 5039-5043, 5063-5071, 5076-5079.  With `n = |y|`, `F = |M|`:
`|psiTEta| ≤ 4F(n+n³)e^{-n²/9}`, hence the two conjuncts with `K = 8`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiTEtaBound : PsiTEtaBound := by
  refine ⟨8, by norm_num, ?_⟩
  intro ν s hν hs hνs M y
  have ha1 := pdc_ageA_ge_one hν.le hs
  have hepos : 0 < Real.exp (-(sq2 y) / (2 * ageA ν s)) := Real.exp_pos _
  have hexp := pdc_exp_le hν.le hs hνs y
  have hw0 : 0 < (ageA ν s ^ 4)⁻¹ := by positivity
  have hw1 : (ageA ν s ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha1)
  have hF := pdc_frob_nonneg M
  have hn := norm_nonneg y
  have hG : 0 < Real.exp (-(‖y‖ ^ 2) / 9) := Real.exp_pos _
  have hQ := pdc_qM_le M y
  have hy1 := pdc_abs_fst_le y
  have hy2 := pdc_abs_snd_le y
  have hM02 := pdc_abs_le_frob M 0 2
  have hM20 := pdc_abs_le_frob M 2 0
  have hM22 := pdc_abs_le_frob M 2 2
  have ha0 : (0 : ℝ) < ageA ν s := by linarith
  -- the first two summands of the bracket
  have hB1 : |(M 0 2 + M 2 0) * y.1 + 2 * M 2 2 * y.2| ≤ 4 * frob M * ‖y‖ := by
    have t1 : |(M 0 2 + M 2 0) * y.1| ≤ 2 * frob M * ‖y‖ := by
      rw [abs_mul]
      have hs2 : |M 0 2 + M 2 0| ≤ 2 * frob M := (abs_add_le _ _).trans (by linarith)
      exact mul_le_mul hs2 hy1 (abs_nonneg _) (by positivity)
    have t2 : |2 * M 2 2 * y.2| ≤ 2 * frob M * ‖y‖ := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hM22 (by norm_num)) hy2 (abs_nonneg _)
        (by positivity)
    have t3 := abs_add_le ((M 0 2 + M 2 0) * y.1) (2 * M 2 2 * y.2)
    linarith
  -- the third summand `(y₂/a) Q_M(y)`
  have hT : |y.2 / ageA ν s * qM M y| ≤ 4 * frob M * ‖y‖ ^ 3 := by
    rw [abs_mul, abs_div, abs_of_pos ha0]
    calc |y.2| / ageA ν s * |qM M y| ≤ |y.2| * |qM M y| :=
          mul_le_mul_of_nonneg_right (div_le_self (abs_nonneg _) ha1) (abs_nonneg _)
      _ ≤ ‖y‖ * (4 * frob M * ‖y‖ ^ 2) := mul_le_mul hy2 hQ (abs_nonneg _) hn
      _ = 4 * frob M * ‖y‖ ^ 3 := by ring
  have hB : |(M 0 2 + M 2 0) * y.1 + 2 * M 2 2 * y.2 - y.2 / ageA ν s * qM M y|
      ≤ 4 * frob M * (‖y‖ + ‖y‖ ^ 3) := by
    have h1 := abs_le.mp hB1
    have h2 := abs_le.mp hT
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hEw : Real.exp (-(sq2 y) / (2 * ageA ν s)) * (ageA ν s ^ 4)⁻¹ ≤ Real.exp (-(‖y‖ ^ 2) / 9) := by
    calc Real.exp (-(sq2 y) / (2 * ageA ν s)) * (ageA ν s ^ 4)⁻¹
        ≤ Real.exp (-(‖y‖ ^ 2) / 9) * 1 := mul_le_mul hexp hw1 hw0.le hG.le
      _ = Real.exp (-(‖y‖ ^ 2) / 9) := mul_one _
  have hpT : |psiTEta ν s M y| ≤ Real.exp (-(‖y‖ ^ 2) / 9) * (4 * frob M * (‖y‖ + ‖y‖ ^ 3)) := by
    unfold psiTEta
    rw [abs_mul, abs_mul, abs_of_pos hepos, abs_of_pos hw0]
    exact mul_le_mul hEw hB (abs_nonneg _) hG.le
  have hc1 : ‖y‖ + ‖y‖ ^ 3 ≤ 2 * (1 + ‖y‖) ^ 4 := by
    nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4]
  have hc2 : ‖y‖ ^ 2 + ‖y‖ ^ 4 ≤ 2 * (1 + ‖y‖) ^ 4 := by
    nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4]
  unfold genvT
  refine ⟨?_, ?_⟩
  · calc |psiTEta ν s M y| ≤ Real.exp (-(‖y‖ ^ 2) / 9) * (4 * frob M * (‖y‖ + ‖y‖ ^ 3)) := hpT
      _ ≤ Real.exp (-(‖y‖ ^ 2) / 9) * (4 * frob M * (2 * (1 + ‖y‖) ^ 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc1 (by positivity)) hG.le
      _ = 8 * frob M * ((1 + ‖y‖) ^ 4 * Real.exp (-(‖y‖ ^ 2) / 9)) := by ring
  · calc |y.2| * |psiTEta ν s M y|
        ≤ ‖y‖ * (Real.exp (-(‖y‖ ^ 2) / 9) * (4 * frob M * (‖y‖ + ‖y‖ ^ 3))) :=
          mul_le_mul hy2 hpT (abs_nonneg _) hn
      _ = Real.exp (-(‖y‖ ^ 2) / 9) * (4 * frob M * (‖y‖ ^ 2 + ‖y‖ ^ 4)) := by ring
      _ ≤ Real.exp (-(‖y‖ ^ 2) / 9) * (4 * frob M * (2 * (1 + ‖y‖) ^ 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc2 (by positivity)) hG.le
      _ = 8 * frob M * ((1 + ‖y‖) ^ 4 * Real.exp (-(‖y‖ ^ 2) / 9)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
