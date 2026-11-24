import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Leaf `PartII-b:T12/1/1/2/3`: local integrability of the planar gradient kernel

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

The gradient kernel is `∂_k N(x) = (2π)⁻¹ x_k / (x₀² + x₁²)`.  With `m = ‖x‖` (sup norm) one has
`m² ≤ s := x₀² + x₁²` and `|x_k| ≤ m`, so `|∂_k N(x)| ≤ (2π)⁻¹ m⁻¹` for all `x ≠ 0`.  Since
`1 < 2 = dim ℝ²`, the bound `‖x‖⁻¹` is locally integrable, and the Mathlib lemma
`MeasureTheory.locallyIntegrable_of_norm_le_rpow` gives the result globally.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

theorem newtonGradKernel_measurable (k : Fin 2) : Measurable (newtonGradKernel k) := by
  unfold newtonGradKernel
  exact (measurable_const.mul (measurable_pi_apply k)).div (by fun_prop)

/-- Pointwise bound `|∂_k N(x)| ≤ (2π)⁻¹ ‖x‖⁻¹` for every `x` in the plane. -/
theorem newtonGradKernel_bound (k : Fin 2) (x : Pl) :
    ‖newtonGradKernel k x‖ ≤ (2 * Real.pi)⁻¹ * ‖x‖⁻¹ := by
  by_cases h0 : x = 0
  · subst h0
    simp [newtonGradKernel]
  have hm : 0 < ‖x‖ := norm_pos_iff.mpr h0
  have hcoord : ∀ i : Fin 2, x i ^ 2 ≤ ‖x‖ ^ 2 := by
    intro i
    have h := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at h
    have := pow_le_pow_left₀ (abs_nonneg (x i)) h 2
    rwa [sq_abs] at this
  -- `‖x‖ ≤ √s`, hence `‖x‖² ≤ s`
  set s : ℝ := x 0 ^ 2 + x 1 ^ 2 with hs_def
  have hp0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
  have hp1 : 0 ≤ x 1 ^ 2 := sq_nonneg _
  have hnorm_le : ‖x‖ ≤ Real.sqrt s := by
    have hcoord' : ∀ i : Fin 2, ‖x i‖ ≤ Real.sqrt s := by
      intro i
      rw [Real.norm_eq_abs]
      apply Real.abs_le_sqrt
      have hc0 : x 0 ^ 2 ≤ s := by rw [hs_def]; linarith
      have hc1 : x 1 ^ 2 ≤ s := by rw [hs_def]; linarith
      fin_cases i
      · exact hc0
      · exact hc1
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg s)).mpr hcoord'
  have hs_ge : ‖x‖ ^ 2 ≤ s := by
    have h := pow_le_pow_left₀ (norm_nonneg x) hnorm_le 2
    rwa [Real.sq_sqrt (by linarith)] at h
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs_ge
  have hfac : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hkx : |x k| ≤ ‖x‖ := by
    have h := norm_le_pi_norm x k
    rwa [Real.norm_eq_abs] at h
  have hkey : ‖x‖⁻¹ * ‖x‖ ^ 2 = ‖x‖ := by
    field_simp
  have hinv_s : ‖x‖ ≤ ‖x‖⁻¹ * s := by
    have hinv : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr (norm_nonneg x)
    nlinarith [hs_ge, hinv]
  unfold newtonGradKernel
  rw [← hs_def, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hfac,
    abs_of_pos hspos]
  rw [div_le_iff₀ hspos]
  have hxk : |x k| ≤ ‖x‖⁻¹ * s := le_trans hkx hinv_s
  calc (2 * Real.pi)⁻¹ * |x k| ≤ (2 * Real.pi)⁻¹ * (‖x‖⁻¹ * s) :=
        mul_le_mul_of_nonneg_left hxk hfac
    _ = (2 * Real.pi)⁻¹ * ‖x‖⁻¹ * s := by ring

/-- **Leaf `PartII-b:T12/1/1/2/3`.**  Each planar gradient kernel `x ↦ (2π)⁻¹ x_k / |x|²` is
locally integrable on the plane. -/
theorem newtonGradKernelLocInt : NewtonGradKernelLocInt := by
  intro k
  have hd : 1 ≤ Module.finrank ℝ Pl := by rw [Module.finrank_fin_fun]; norm_num
  have hα : (1 : ℝ) < (Module.finrank ℝ Pl : ℝ) := by rw [Module.finrank_fin_fun]; norm_num
  have hdecay : ∀ᵐ x ∂(volume : Measure Pl),
      ‖newtonGradKernel k x‖ ≤ (2 * Real.pi)⁻¹ * ‖x‖ ^ (-(1 : ℝ)) := by
    filter_upwards with x
    rw [Real.rpow_neg_one]
    exact newtonGradKernel_bound k x
  exact locallyIntegrable_of_norm_le_rpow hd hα hdecay
    (newtonGradKernel_measurable k).aestronglyMeasurable

end UnforcedLeray.Short.IIb.PlaneRiesz
