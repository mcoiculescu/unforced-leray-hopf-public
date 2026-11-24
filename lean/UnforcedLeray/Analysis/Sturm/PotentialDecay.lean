import UnforcedLeray.Analysis.Sturm.QuadraticForm

/-!
# Decay of the actual Gaussian log-radius potential

These are limits of the explicitly defined potential, not decay assumptions.
They are inputs for the compactness of a potential perturbation of the free
one-dimensional resolvent; compactness itself is not asserted here.
-/

noncomputable section
open Filter
open scoped Topology
namespace UnforcedLeray.Sturm
open GaussianPotential

/-- The removable-completed radial-parameter potential vanishes at infinity. -/
theorem tendsto_W_atTop : Tendsto W atTop (𝓝 0) := by
  have h2 := Real.tendsto_div_pow_mul_exp_add_atTop 1 (-1) 2 (by norm_num)
  have h1 := Real.tendsto_div_pow_mul_exp_add_atTop 1 (-1) 1 (by norm_num)
  have hsum := (h2.const_mul 4).add (h1.const_mul 8)
  simp only [one_mul, pow_one, mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  simp only [W, ne_of_gt hy, ↓reduceIte]
  ring

/-- At the left radial endpoint the ordinary quotient has no singularity. -/
theorem tendsto_W_at_minus_two : Tendsto W (𝓝 (-2 : ℝ)) (𝓝 0) := by
  have hden : Real.exp (-2 : ℝ) - 1 ≠ 0 := by
    have h : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hrat := (((tendsto_id.add_const 2).const_mul 4).mul tendsto_id).div
    ((Real.continuous_exp.tendsto (-2 : ℝ)).sub_const 1) hden
  norm_num only [neg_add_cancel, mul_zero, zero_mul, zero_div] at hrat
  apply hrat.congr'
  filter_upwards [eventually_ne_nhds (show (-2 : ℝ) ≠ 0 by norm_num)] with y hy
  simp only [W, hy, ↓reduceIte]
  rfl

/-- The log-radius potential decays at the large-radius end. -/
theorem tendsto_Wlog_atTop : Tendsto Wlog atTop (𝓝 0) := by
  apply tendsto_W_atTop.comp
  have hlin : Tendsto (fun t : ℝ => 2 * t) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hdiv : Tendsto (fun t : ℝ => Real.exp (2 * t) / 4) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num : 0 < (4 : ℝ))
      (Real.tendsto_exp_atTop.comp hlin)
  simpa only [sub_eq_add_neg] using hdiv.atTop_add (tendsto_const_nhds (x := (-2 : ℝ)))

/-- The log-radius potential also decays at the zero-radius end. -/
theorem tendsto_Wlog_atBot : Tendsto Wlog atBot (𝓝 0) := by
  apply tendsto_W_at_minus_two.comp
  have hlin : Tendsto (fun t : ℝ => 2 * t) atBot atBot :=
    tendsto_id.const_mul_atBot (by norm_num)
  have h := ((Real.tendsto_exp_atBot.comp hlin).div_const 4).sub_const 2
  simpa using h

end UnforcedLeray.Sturm
