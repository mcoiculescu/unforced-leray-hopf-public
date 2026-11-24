import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4_1

/-!
# `PartIII-a:T21/c1/a/4/1`: the right dominated-convergence leaf `ExtRightDCT`

Source: `the November 2 reference manuscript`
lines 603-610. `seedEll h F = (seedJ h)⁻¹ * ∫_{(0,∞)} h F / k * r`. The constant `(seedJ h)⁻¹`
passes through the limit. The integrand is dominated by `(|Cw| |C|) r exp(-r²/8)` (the factor
`h/k` is bounded by `Cw` where `k ≠ 0`, and the integrand vanishes where `k = 0` in Lean).
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set

theorem extRightDCT_proof : UnforcedLeray.Short.IIIa.ExtRightDCT := by
  intro h Cw hhmeas hCw F Finf C hFmeas hFb hFpt
  unfold UnforcedLeray.Short.PartI.seedEll
  apply Tendsto.const_mul
  have hkc : Continuous (fun r : ℝ => ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ)) := by
    unfold UnforcedLeray.Blueprint.Planar.strainK
    fun_prop
  have hkinv : Measurable (fun r : ℝ => (((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ))⁻¹) :=
    hkc.measurable.inv
  have hbound_int : Integrable
      (fun r : ℝ => (|Cw| * |C|) * (r * Real.exp (-(1 / 8 : ℝ) * r ^ 2)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 8)).const_mul
      (|Cw| * |C|)).integrableOn
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun r : ℝ => h r * F n r / ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ) * (r : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    have e : (fun r : ℝ => h r * F n r / ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ) * (r : ℂ))
        = fun r : ℝ => ((h r * F n r) * (((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ))⁻¹)
            * (r : ℂ) := by
      funext r
      ring
    rw [e]
    refine ((hhmeas.mul (hFmeas n)).mul hkinv.aestronglyMeasurable).mul ?_
    exact (Complex.continuous_ofReal.measurable).aestronglyMeasurable
  refine tendsto_integral_of_dominated_convergence
    (fun r : ℝ => (|Cw| * |C|) * (r * Real.exp (-(1 / 8 : ℝ) * r ^ 2))) hmeas hbound_int ?_ ?_
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : (0 : ℝ) < r := hr
    by_cases hk0 : UnforcedLeray.Blueprint.Planar.strainK r = 0
    · simp only [hk0, Complex.ofReal_zero, div_zero, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg hr'.le (Real.exp_pos _).le)
    · have hbnd := hCw r hr' hk0
      have hFr := hFb n r hr'
      have hE : -(r ^ 2) / 8 = -(1 / 8 : ℝ) * r ^ 2 := by ring
      rw [hE] at hFr
      have e : h r * F n r / ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ) * (r : ℂ)
          = (h r / ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ)) * F n r * (r : ℂ) := by
        ring
      rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr'.le]
      have hCabs : C * Real.exp (-(1 / 8 : ℝ) * r ^ 2)
          ≤ |C| * Real.exp (-(1 / 8 : ℝ) * r ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      have h1 : ‖h r / ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ)‖ ≤ |Cw| :=
        hbnd.trans (le_abs_self Cw)
      have h2 : ‖F n r‖ ≤ |C| * Real.exp (-(1 / 8 : ℝ) * r ^ 2) := hFr.trans hCabs
      calc ‖h r / ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ)‖ * ‖F n r‖ * r
          ≤ |Cw| * (|C| * Real.exp (-(1 / 8 : ℝ) * r ^ 2)) * r := by
            apply mul_le_mul_of_nonneg_right _ hr'.le
            exact mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg _)
        _ = (|Cw| * |C|) * (r * Real.exp (-(1 / 8 : ℝ) * r ^ 2)) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : (0 : ℝ) < r := hr
    have e1 : ∀ n, h r * F n r / ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ) * (r : ℂ)
        = (h r / ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ) * (r : ℂ)) * F n r := by
      intro n
      ring
    have e2 : h r * Finf r / ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ) * (r : ℂ)
        = (h r / ((UnforcedLeray.Blueprint.Planar.strainK r : ℝ) : ℂ) * (r : ℂ)) * Finf r := by
      ring
    simp only [e1, e2]
    exact Tendsto.const_mul _ (hFpt r hr')
