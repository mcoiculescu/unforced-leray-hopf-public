import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Leaf `PartII-b:T12/1/1/2/19`: the pointwise bound for the planar Riesz kernel

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

The kernel is `K_{ik}(x) = (2π)⁻¹ (δ_{ik} s - 2 x_i x_k) / s²` for `x ≠ 0`, where
`s = x₀² + x₁²` is the Euclidean square.  Since `x_j² ≤ s` for each `j` and `|δ_{ik}| ≤ 1`,
the numerator is at most `3 s` in absolute value, so `|K_{ik}(x)| ≤ 3 (2π)⁻¹ s⁻¹`.  If
`δ ≤ ‖x‖` (sup norm), then `δ² ≤ ‖x‖² ≤ s`, and `3 (2π)⁻¹ ≤ 1` gives `|K_{ik}(x)| ≤ (δ²)⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/19`.**  For `0 < δ ≤ ‖z‖`, `|K_{ik}(z)| ≤ (δ²)⁻¹`. -/
theorem planeRieszKernelBound : PlaneRieszKernelBound := by
  intro i k δ z hδ hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hz
    linarith
  -- the Euclidean square `s` dominates each squared coordinate and `‖z‖²`
  have hp0 : 0 ≤ z 0 ^ 2 := sq_nonneg _
  have hp1 : 0 ≤ z 1 ^ 2 := sq_nonneg _
  set s : ℝ := z 0 ^ 2 + z 1 ^ 2 with hs_def
  have hc : ∀ j : Fin 2, z j ^ 2 ≤ s := by
    have hc0 : z 0 ^ 2 ≤ s := by rw [hs_def]; linarith
    have hc1 : z 1 ^ 2 ≤ s := by rw [hs_def]; linarith
    intro j
    fin_cases j
    · exact hc0
    · exact hc1
  have hnorm_le : ‖z‖ ≤ Real.sqrt s := by
    have hcoord' : ∀ j : Fin 2, ‖z j‖ ≤ Real.sqrt s := by
      intro j
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (hc j)
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg s)).mpr hcoord'
  have hδs : δ ^ 2 ≤ s := by
    have h := pow_le_pow_left₀ hδ.le (le_trans hz hnorm_le) 2
    rwa [Real.sq_sqrt (by linarith)] at h
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hδs
  have hfac : 0 < (2 * Real.pi)⁻¹ := by positivity
  -- the numerator is bounded by `3 s`
  have hc_abs : |(if i = k then (1 : ℝ) else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  have hcs : |(if i = k then (1 : ℝ) else 0) * s| ≤ s := by
    rw [abs_mul, abs_of_pos hspos]
    exact mul_le_of_le_one_left hspos.le hc_abs
  have hcross : |2 * z i * z k| ≤ 2 * s := by
    have h1 : |2 * z i * z k| ≤ z i ^ 2 + z k ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (z i + z k), sq_nonneg (z i - z k)]
    linarith [hc i, hc k]
  have hnum : |(if i = k then (1 : ℝ) else 0) * s - 2 * z i * z k| ≤ 3 * s := by
    have h1 := abs_le.mp hcs
    have h2 := abs_le.mp hcross
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  unfold planeRieszKernel
  rw [if_neg hz0]
  rw [← hs_def]
  rw [abs_div, abs_mul, abs_of_pos hfac, abs_of_pos (pow_pos hspos 2)]
  rw [div_le_iff₀ (pow_pos hspos 2)]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hB : (2 * Real.pi)⁻¹ * (3 * s) ≤ (δ ^ 2)⁻¹ * s ^ 2 := by
    have hδ2 : 0 < δ ^ 2 := by positivity
    have e1 : (2 * Real.pi)⁻¹ * (3 * s) = (3 * s) / (2 * Real.pi) := by ring
    have e2 : (δ ^ 2)⁻¹ * s ^ 2 = s ^ 2 / δ ^ 2 := by ring
    rw [e1, e2, div_le_div_iff₀ (by positivity) hδ2]
    nlinarith [mul_le_mul_of_nonneg_left hδs hspos.le, mul_nonneg (sub_nonneg.mpr hpi.le) (sq_nonneg s)]
  calc (2 * Real.pi)⁻¹ * |(if i = k then (1 : ℝ) else 0) * s - 2 * z i * z k|
      ≤ (2 * Real.pi)⁻¹ * (3 * s) := mul_le_mul_of_nonneg_left hnum hfac.le
    _ ≤ (δ ^ 2)⁻¹ * s ^ 2 := hB

end UnforcedLeray.Short.IIb.PlaneRiesz
