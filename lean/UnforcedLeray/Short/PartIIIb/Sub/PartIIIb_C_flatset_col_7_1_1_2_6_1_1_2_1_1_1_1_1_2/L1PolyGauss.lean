import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1_2

/-!
# Polynomial moments of the Gaussian (`T0gPolyGauss`)

Source `the November 2 reference manuscript`
lines 1640-1656. Proof: `(1+u)^n e^{-u^2/8} ≤ K_n` (Gaussian.add_one_pow_mul_exp_le) applied at
`u = ‖w‖`, after splitting `e^{-w²/4} = e^{-w²/8} · e^{-w²/8}`, so the integrand is dominated by
a constant times `e^{-w²/8}`, which is integrable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

theorem t0g_polyGauss :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gPolyGauss := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gPolyGauss
  intro N
  obtain ⟨K, hK0, hK⟩ := UnforcedLeray.Gaussian.add_one_pow_mul_exp_le N
  have hG : Integrable (fun w : UnforcedLeray.Gaussian.Euc 2 =>
      Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2)) :=
    UnforcedLeray.Gaussian.integrable_exp_neg_mul_sq_norm (d := 2) (b := 1 / 8) (by norm_num)
  refine (hG.const_mul ((4 * Real.pi * 1) ^ (-((2 : ℕ) : ℝ) / 2) * K)).mono' ?_
    (Eventually.of_forall fun w => ?_)
  · exact (((continuous_const.add continuous_norm).pow N).mul
      (UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) 1)).aestronglyMeasurable
  · have hnn : 0 ≤ (1 + ‖w‖) ^ N * UnforcedLeray.Gaussian.gaussKernel 2 1 w :=
      mul_nonneg (pow_nonneg (by positivity) _)
        (UnforcedLeray.Gaussian.gaussKernel_nonneg zero_lt_one w)
    rw [Real.norm_of_nonneg hnn, UnforcedLeray.Gaussian.gaussKernel_eq_exp]
    have h2 : Real.exp (-(4 * 1 : ℝ)⁻¹ * ‖w‖ ^ 2)
        = Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    have h3 : (1 + ‖w‖) ^ N * Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2) ≤ K := by
      have h := hK ‖w‖ (norm_nonneg w)
      rw [← neg_mul] at h
      rw [add_comm]
      exact h
    have he : 0 ≤ Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2) := (Real.exp_pos _).le
    have hc : 0 ≤ (4 * Real.pi * 1 : ℝ) ^ (-((2 : ℕ) : ℝ) / 2) := by positivity
    have h4 : (1 + ‖w‖) ^ N * Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2)
        ≤ K * Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h3 he
    calc _ = (4 * Real.pi * 1) ^ (-((2 : ℕ) : ℝ) / 2) *
            ((1 + ‖w‖) ^ N * Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2) *
              Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2)) := by ring
      _ ≤ (4 * Real.pi * 1) ^ (-((2 : ℕ) : ℝ) / 2) * (K * Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h4 hc
      _ = (4 * Real.pi * 1) ^ (-((2 : ℕ) : ℝ) / 2) * K * Real.exp (-(1 / 8 : ℝ) * ‖w‖ ^ 2) := by ring

end
