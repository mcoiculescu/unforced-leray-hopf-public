import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Defs

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4/1/5` leaf: the `s`-derivative envelope of one lattice term

Source `the November 2 reference manuscript`
lines 4978, 5039-5043, 5063-5071, 5076-5079: the weight `s` of `𝒦`, and `∂_s a = ν`, `νs ≤ 5/2`.
Constant `K = 60`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiTSBound : PsiTSBound := by
  refine ⟨60, by norm_num, fun ν s hν hs hνs M D y => ?_⟩
  have ha1 : 1 ≤ ageA ν s := pdc_ageA_ge_one hν.le hs
  have hapos : 0 < ageA ν s := by linarith
  have hE : Real.exp (-(sq2 y) / (2 * ageA ν s)) ≤ Real.exp (-(‖y‖ ^ 2) / 9) :=
    pdc_exp_le hν.le hs hνs y
  have hE0 : 0 ≤ Real.exp (-(sq2 y) / (2 * ageA ν s)) := (Real.exp_pos _).le
  have hW0 : 0 ≤ Real.exp (-(‖y‖ ^ 2) / 9) := (Real.exp_pos _).le
  have hn : 0 ≤ ‖y‖ := norm_nonneg y
  have hF : 0 ≤ frob M := pdc_frob_nonneg M
  have hG : 0 ≤ frob (s • D) := pdc_frob_nonneg _
  have ha4 : 0 ≤ (ageA ν s ^ 4)⁻¹ := by positivity
  have ha4le : (ageA ν s ^ 4)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ ha1
  -- `s · psiTS` with `s·qM D = qM (s • D)`
  have key : s * psiTS ν s M D y =
      Real.exp (-(sq2 y) / (2 * ageA ν s)) * (ageA ν s ^ 4)⁻¹ *
        (qM (s • D) y - (4 * ν * s / ageA ν s) * qM M y +
          ((ν * s) * sq2 y / (2 * ageA ν s ^ 2)) * qM M y) := by
    unfold psiTS
    rw [pdc_qM_smul]
    ring
  -- coefficient bounds
  have hc1 : |qM (s • D) y| ≤ 4 * frob (s • D) * ‖y‖ ^ 2 := pdc_qM_le _ _
  have hM : |qM M y| ≤ 4 * frob M * ‖y‖ ^ 2 := pdc_qM_le M y
  have hk0 : 0 ≤ 4 * ν * s / ageA ν s := by
    have : 0 ≤ ν * s := mul_nonneg hν.le hs
    positivity
  have hk : 4 * ν * s / ageA ν s ≤ 10 := by
    have h := div_le_self (by positivity : (0 : ℝ) ≤ 4 * ν * s) ha1
    linarith
  have hc0 : 0 ≤ (ν * s) * sq2 y / (2 * ageA ν s ^ 2) := by
    have : 0 ≤ ν * s := mul_nonneg hν.le hs
    have := pdc_sq2_nonneg y
    positivity
  have hc : (ν * s) * sq2 y / (2 * ageA ν s ^ 2) ≤ 5 / 2 * ‖y‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (ν * s) * sq2 y ≤ 5 / 2 * (2 * ‖y‖ ^ 2) :=
      mul_le_mul hνs (pdc_sq2_le y) (pdc_sq2_nonneg y) (by norm_num)
    have h2 : 0 ≤ ‖y‖ ^ 2 * (ageA ν s ^ 2 - 1) :=
      mul_nonneg (sq_nonneg _) (by nlinarith)
    nlinarith
  -- bound on the bracket
  have t3 : |(4 * ν * s / ageA ν s) * qM M y| ≤ 10 * (4 * frob M * ‖y‖ ^ 2) := by
    rw [abs_mul, abs_of_nonneg hk0]
    exact mul_le_mul hk hM (abs_nonneg _) (by norm_num)
  have t4 : |((ν * s) * sq2 y / (2 * ageA ν s ^ 2)) * qM M y|
      ≤ 5 / 2 * ‖y‖ ^ 2 * (4 * frob M * ‖y‖ ^ 2) := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul hc hM (abs_nonneg _) (by positivity)
  have hB : |qM (s • D) y - (4 * ν * s / ageA ν s) * qM M y +
      ((ν * s) * sq2 y / (2 * ageA ν s ^ 2)) * qM M y|
      ≤ 4 * frob (s • D) * ‖y‖ ^ 2 + 10 * (4 * frob M * ‖y‖ ^ 2)
        + 5 / 2 * ‖y‖ ^ 2 * (4 * frob M * ‖y‖ ^ 2) := by
    have t1 := abs_add_le (qM (s • D) y - (4 * ν * s / ageA ν s) * qM M y)
      (((ν * s) * sq2 y / (2 * ageA ν s ^ 2)) * qM M y)
    have t2 := abs_sub (qM (s • D) y) ((4 * ν * s / ageA ν s) * qM M y)
    linarith
  -- polynomial comparison with the envelope
  have h2 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 4 := by
    have a1 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := pow_le_pow_left₀ hn (by linarith) 2
    have a2 : (1 + ‖y‖) ^ 2 ≤ (1 + ‖y‖) ^ 4 := by
      have : 1 ≤ (1 + ‖y‖) := by linarith
      nlinarith [pow_le_pow_right₀ this (by norm_num : 2 ≤ 4)]
    linarith
  have h4 : ‖y‖ ^ 4 ≤ (1 + ‖y‖) ^ 4 := pow_le_pow_left₀ hn (by linarith) 4
  have hT0 : 0 ≤ (1 + ‖y‖) ^ 4 := by positivity
  have g1 : frob (s • D) * ‖y‖ ^ 2 ≤ frob (s • D) * (1 + ‖y‖) ^ 4 :=
    mul_le_mul_of_nonneg_left h2 hG
  have f1 : frob M * ‖y‖ ^ 2 ≤ frob M * (1 + ‖y‖) ^ 4 :=
    mul_le_mul_of_nonneg_left h2 hF
  have f2 : frob M * ‖y‖ ^ 4 ≤ frob M * (1 + ‖y‖) ^ 4 :=
    mul_le_mul_of_nonneg_left h4 hF
  have hBT : 4 * frob (s • D) * ‖y‖ ^ 2 + 10 * (4 * frob M * ‖y‖ ^ 2)
      + 5 / 2 * ‖y‖ ^ 2 * (4 * frob M * ‖y‖ ^ 2)
      ≤ 60 * (frob M + frob (s • D)) * (1 + ‖y‖) ^ 4 := by
    have gT : 0 ≤ frob (s • D) * (1 + ‖y‖) ^ 4 := mul_nonneg hG hT0
    have fT : 0 ≤ frob M * (1 + ‖y‖) ^ 4 := mul_nonneg hF hT0
    nlinarith
  -- assembly
  have habs : s * |psiTS ν s M D y| = |s * psiTS ν s M D y| := by
    rw [abs_mul, abs_of_nonneg hs]
  have hPW : Real.exp (-(sq2 y) / (2 * ageA ν s)) * (ageA ν s ^ 4)⁻¹ ≤
      Real.exp (-(‖y‖ ^ 2) / 9) :=
    (mul_le_of_le_one_right hE0 ha4le).trans hE
  have hP0 : 0 ≤ Real.exp (-(sq2 y) / (2 * ageA ν s)) * (ageA ν s ^ 4)⁻¹ :=
    mul_nonneg hE0 ha4
  rw [habs, key]
  calc |Real.exp (-(sq2 y) / (2 * ageA ν s)) * (ageA ν s ^ 4)⁻¹ *
        (qM (s • D) y - (4 * ν * s / ageA ν s) * qM M y +
          ((ν * s) * sq2 y / (2 * ageA ν s ^ 2)) * qM M y)|
      = (Real.exp (-(sq2 y) / (2 * ageA ν s)) * (ageA ν s ^ 4)⁻¹) *
          |qM (s • D) y - (4 * ν * s / ageA ν s) * qM M y +
          ((ν * s) * sq2 y / (2 * ageA ν s ^ 2)) * qM M y| := by
        rw [abs_mul, abs_of_nonneg hP0]
    _ ≤ Real.exp (-(‖y‖ ^ 2) / 9) *
          |qM (s • D) y - (4 * ν * s / ageA ν s) * qM M y +
          ((ν * s) * sq2 y / (2 * ageA ν s ^ 2)) * qM M y| :=
        mul_le_mul_of_nonneg_right hPW (abs_nonneg _)
    _ ≤ Real.exp (-(‖y‖ ^ 2) / 9) *
          (4 * frob (s • D) * ‖y‖ ^ 2 + 10 * (4 * frob M * ‖y‖ ^ 2)
            + 5 / 2 * ‖y‖ ^ 2 * (4 * frob M * ‖y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hB hW0
    _ ≤ Real.exp (-(‖y‖ ^ 2) / 9) *
          (60 * (frob M + frob (s • D)) * (1 + ‖y‖) ^ 4) :=
        mul_le_mul_of_nonneg_left hBT hW0
    _ = 60 * (frob M + frob (s • D)) * genvT y := by
        unfold genvT
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
