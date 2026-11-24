import UnforcedLeray.Lib.HeatCylinder.H3Operator

/-!
# Local uniform bounds for positive-time cylinder heat-divergence orbits

The Gaussian-gradient smoothing coefficient is continuous and decreasing in positive heat age.
These facts provide the local operator bounds needed for a smooth-density continuity argument.
-/

set_option autoImplicit false

namespace UnforcedLeray.HeatCylinder

open Set

/-- The actual Gaussian-gradient `L²` coefficient is continuous at every positive heat age. -/
theorem continuousOn_heatDivL2Coeff : ContinuousOn heatDivL2Coeff (Ioi 0) := by
  unfold heatDivL2Coeff
  have harg : Continuous (fun θ : ℝ => 4 * Real.pi * 1 * θ) := by
    fun_prop
  have hden : ContinuousOn (fun θ : ℝ => Real.sqrt (4 * Real.pi * 1 * θ)) (Ioi 0) :=
    (Real.continuous_sqrt.comp harg).continuousOn
  have hnonzero : ∀ θ ∈ Ioi (0 : ℝ), Real.sqrt (4 * Real.pi * 1 * θ) ≠ 0 := by
    intro θ hθ
    have hp : 0 < 4 * Real.pi * 1 * θ :=
      mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos)
        (by norm_num)) hθ
    exact (Real.sqrt_pos.2 hp).ne'
  exact continuousOn_const.mul (hden.inv₀ hnonzero)

/-- The heat-divergence smoothing coefficient decreases as the positive heat age increases. -/
theorem heatDivL2Coeff_le_of_le {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hle : a ≤ θ) :
    heatDivL2Coeff θ ≤ heatDivL2Coeff a := by
  have harg : 4 * Real.pi * 1 * a ≤ 4 * Real.pi * 1 * θ := by gcongr
  have hden : Real.sqrt (4 * Real.pi * 1 * a) ≤ Real.sqrt (4 * Real.pi * 1 * θ) :=
    Real.sqrt_le_sqrt harg
  have hdenA : 0 < Real.sqrt (4 * Real.pi * 1 * a) := by positivity
  have hdenT : 0 < Real.sqrt (4 * Real.pi * 1 * θ) := by positivity
  have hinv : (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ ≤
      (Real.sqrt (4 * Real.pi * 1 * a))⁻¹ :=
    by simpa [one_div] using one_div_le_one_div_of_le hdenA hden
  unfold heatDivL2Coeff
  exact mul_le_mul_of_nonneg_left hinv (by norm_num)

/-- On any positive-age interval `[a,∞)`, the actual H³ operator norm is bounded by the
period-independent coefficient at the left endpoint. -/
theorem norm_actualHeatDivH3CLM_le_at_left {c a θ : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hθ : 0 < θ) (hle : a ≤ θ) (x : UnforcedLeray.TrainB.TensorH3 c) :
    ‖actualHeatDivH3CLM hc hθ x‖ ≤
      (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff a)).toReal * ‖x‖ := by
  have hbase := norm_actualHeatDivH3_le hc hθ x
  have hcoeff := heatDivL2Coeff_le_of_le ha hθ hle
  have hnorm : 0 ≤ ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ := norm_nonneg _
  have hmul : ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
      ENNReal.ofReal (heatDivL2Coeff θ) ≤
      ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
      ENNReal.ofReal (heatDivL2Coeff a) := by
    gcongr
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hmul
  exact hbase.trans (mul_le_mul_of_nonneg_right hreal (norm_nonneg x))

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.continuousOn_heatDivL2Coeff
#print axioms UnforcedLeray.HeatCylinder.heatDivL2Coeff_le_of_le
#print axioms UnforcedLeray.HeatCylinder.norm_actualHeatDivH3CLM_le_at_left
