import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Leaf `PartII-b:T12/1/1/2/2`: local integrability of the planar Newton kernel

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

The planar Newton kernel is `N(x) = (4π)⁻¹ log (x₀² + x₁²)`.  We prove that it is locally
integrable on the plane `Fin 2 → ℝ` (sup-norm gauge, Lebesgue measure).  On a sup-norm ball
`‖x‖ < R` with `x ≠ 0` and `m = ‖x‖`, one has `m² ≤ s := x₀² + x₁² ≤ 2m²`, hence
`-2 m⁻¹ ≤ log s ≤ 2 R³ m⁻¹`, so `|N(x)| ≤ C ‖x‖⁻¹`, and `‖x‖⁻¹` is integrable on the ball
since the exponent `1 < 2 = dim`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

theorem newtonKernel_measurable : Measurable newtonKernel := by
  unfold newtonKernel
  exact measurable_const.mul (Measurable.log (by fun_prop))

/-- Pointwise bound on a sup-norm ball: `|N(x)| ≤ C ‖x‖⁻¹`. -/
theorem newtonKernel_bound (R : ℝ) (x : Pl) (hx : ‖x‖ < R) :
    ‖newtonKernel x‖ ≤ (4 * Real.pi)⁻¹ * (2 + 2 * R ^ 3) * ‖x‖⁻¹ := by
  by_cases h0 : x = 0
  · subst h0
    simp [newtonKernel]
  have hm : 0 < ‖x‖ := norm_pos_iff.mpr h0
  set s : ℝ := x 0 ^ 2 + x 1 ^ 2 with hs_def
  -- each coordinate is bounded by the norm, so `x i ^ 2 ≤ ‖x‖ ^ 2`
  have hcoord : ∀ i : Fin 2, x i ^ 2 ≤ ‖x‖ ^ 2 := by
    intro i
    have h := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at h
    have := pow_le_pow_left₀ (abs_nonneg (x i)) h 2
    rwa [sq_abs] at this
  have hs_le : s ≤ 2 * ‖x‖ ^ 2 := by
    have h0' := hcoord 0
    have h1' := hcoord 1
    rw [hs_def]
    linarith
  -- the norm is at most the square root of `s`, so `‖x‖² ≤ s`
  have hnorm_le : ‖x‖ ≤ Real.sqrt s := by
    have hcoord' : ∀ i : Fin 2, ‖x i‖ ≤ Real.sqrt s := by
      intro i
      rw [Real.norm_eq_abs]
      apply Real.abs_le_sqrt
      have hp0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
      have hp1 : 0 ≤ x 1 ^ 2 := sq_nonneg _
      have hc0 : x 0 ^ 2 ≤ s := by rw [hs_def]; linarith
      have hc1 : x 1 ^ 2 ≤ s := by rw [hs_def]; linarith
      fin_cases i
      · exact hc0
      · exact hc1
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg s)).mpr hcoord'
  have hs_ge : ‖x‖ ^ 2 ≤ s := by
    have h := pow_le_pow_left₀ (norm_nonneg x) hnorm_le 2
    rwa [Real.sq_sqrt (by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)])] at h
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs_ge
  -- upper bound for log s
  have hup : Real.log s ≤ 2 * R ^ 3 * ‖x‖⁻¹ := by
    have h1 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
    have h2 : 2 * ‖x‖ ^ 3 * ‖x‖⁻¹ = 2 * ‖x‖ ^ 2 := by
      field_simp
    have h3 : ‖x‖ ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ (norm_nonneg x) hx.le 3
    have h4 : 2 * ‖x‖ ^ 2 ≤ 2 * R ^ 3 * ‖x‖⁻¹ := by
      rw [← h2]
      have : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr (norm_nonneg x)
      nlinarith
    linarith
  -- lower bound for log s
  have hlow : -(2 * ‖x‖⁻¹) ≤ Real.log s := by
    have hlog_sq : Real.log (‖x‖ ^ 2) ≤ Real.log s :=
      Real.log_le_log (by positivity) hs_ge
    rw [Real.log_pow] at hlog_sq
    have hinv : Real.log ‖x‖⁻¹ ≤ ‖x‖⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hm)
    rw [Real.log_inv] at hinv
    push_cast at hlog_sq
    nlinarith
  -- assemble
  have hlog_abs : |Real.log s| ≤ (2 + 2 * R ^ 3) * ‖x‖⁻¹ := by
    have hinv_nn : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr (norm_nonneg x)
    rw [abs_le]
    constructor
    · nlinarith [pow_nonneg (norm_nonneg x) 3, pow_nonneg (le_of_lt (by linarith : (0:ℝ) < R)) 3]
    · nlinarith
  have hfactor : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  unfold newtonKernel
  rw [← hs_def, Real.norm_eq_abs, abs_mul, abs_of_nonneg hfactor]
  calc (4 * Real.pi)⁻¹ * |Real.log s|
      ≤ (4 * Real.pi)⁻¹ * ((2 + 2 * R ^ 3) * ‖x‖⁻¹) :=
        mul_le_mul_of_nonneg_left hlog_abs hfactor
    _ = (4 * Real.pi)⁻¹ * (2 + 2 * R ^ 3) * ‖x‖⁻¹ := by ring

/-- **Leaf `PartII-b:T12/1/1/2/2`.**  The planar Newton kernel `N(x) = (4π)⁻¹ log(x₀² + x₁²)`
is locally integrable on the plane. -/
theorem newtonKernelLocInt : NewtonKernelLocInt := by
  unfold NewtonKernelLocInt
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR_pos, hR⟩ := hK.isBounded.exists_pos_norm_lt
  have hd : 1 ≤ Module.finrank ℝ Pl := by rw [Module.finrank_fin_fun]; norm_num
  have hα : (1 : ℝ) < (Module.finrank ℝ Pl : ℝ) := by rw [Module.finrank_fin_fun]; norm_num
  have hdecay : ∀ᵐ x ∂(volume : Measure Pl).restrict (Metric.ball (0 : Pl) R),
      ‖newtonKernel x‖ ≤ (4 * Real.pi)⁻¹ * (2 + 2 * R ^ 3) * ‖x‖ ^ (-(1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxR : ‖x‖ < R := by simpa using hx
    rw [Real.rpow_neg_one]
    exact newtonKernel_bound R x hxR
  have hint : IntegrableOn newtonKernel (Metric.ball (0 : Pl) R) volume :=
    integrableOn_ball_of_norm_le_rpow hd hα hdecay newtonKernel_measurable.aestronglyMeasurable
  exact hint.mono_set (fun x hx => mem_ball_zero_iff.mpr (hR x hx))

end UnforcedLeray.Short.IIb.PlaneRiesz
