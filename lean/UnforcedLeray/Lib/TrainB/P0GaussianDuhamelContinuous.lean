import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelContinuity

/-!
# Continuous target-time path for the actual projected Duhamel term

The positive-time fixed-lag argument and the square-root estimate at zero combine to give a
continuous H³-valued path. Nonpositive target times have an empty causal interval.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

/-- The actual projected nonlinear Duhamel integral is continuous in target time for a globally
bounded continuous tensor path. -/
theorem continuous_projectedHeatDuhamelIntegral {c ν M : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hM : 0 ≤ M)
    (F : ContinuousMap ℝ (TensorH3 c)) (hF : ∀ r, ‖F r‖ ≤ M) :
    Continuous (fun t => projectedHeatDuhamelIntegral (ν := ν) hc F t) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  rcases lt_trichotomy t₀ 0 with ht₀neg | ht₀zero | ht₀pos
  · have hzero : projectedHeatDuhamelIntegral (ν := ν) hc F t₀ = 0 := by
      unfold projectedHeatDuhamelIntegral
      simp [Ioo_eq_empty_of_le ht₀neg.le]
    have hevent : (fun t => projectedHeatDuhamelIntegral (ν := ν) hc F t) =ᶠ[𝓝 t₀]
        fun _ => (0 : VectorH3 c) := by
      filter_upwards [Iio_mem_nhds ht₀neg] with t ht
      have hIoo : Ioo (0 : ℝ) t = ∅ := Ioo_eq_empty_of_le ht.le
      simp [projectedHeatDuhamelIntegral, hIoo]
    change Tendsto (fun t => projectedHeatDuhamelIntegral (ν := ν) hc F t)
      (𝓝 t₀) (𝓝 (projectedHeatDuhamelIntegral (ν := ν) hc F t₀))
    rw [hzero]
    exact tendsto_const_nhds.congr' hevent.symm
  · subst t₀
    exact continuousAt_projectedHeatDuhamelIntegral_zero hc hν hM F hF
  · exact continuousAt_projectedHeatDuhamelIntegral_pos hc hν ht₀pos hM F hF

/-- The continuous-map packaging of the actual projected Duhamel path. -/
noncomputable def projectedHeatDuhamelContinuousMap {c ν M : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hM : 0 ≤ M)
    (F : ContinuousMap ℝ (TensorH3 c)) (hF : ∀ r, ‖F r‖ ≤ M) :
    ContinuousMap ℝ (VectorH3 c) :=
  ⟨fun t => projectedHeatDuhamelIntegral (ν := ν) hc F t,
    continuous_projectedHeatDuhamelIntegral hc hν hM F hF⟩

@[simp]
theorem projectedHeatDuhamelContinuousMap_apply {c ν M : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hM : 0 ≤ M)
    (F : ContinuousMap ℝ (TensorH3 c)) (hF : ∀ r, ‖F r‖ ≤ M) (t : ℝ) :
    projectedHeatDuhamelContinuousMap hc hν hM F hF t =
      projectedHeatDuhamelIntegral (ν := ν) hc F t := rfl

#print axioms UnforcedLeray.TrainB.continuous_projectedHeatDuhamelIntegral
#print axioms UnforcedLeray.TrainB.projectedHeatDuhamelContinuousMap

end UnforcedLeray.TrainB
