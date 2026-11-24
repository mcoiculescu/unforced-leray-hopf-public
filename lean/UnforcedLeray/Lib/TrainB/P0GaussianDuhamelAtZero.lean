import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelGenericBound

/-!
# Continuity of the actual Duhamel term at zero

The explicit square-root-time bound forces the actual nonlinear Volterra integral to vanish
continuously at the initial time, for any globally bounded continuous tensor path.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

/-- The actual projected Gaussian Duhamel integral is continuous at the initial time. -/
theorem continuousAt_projectedHeatDuhamelIntegral_zero {c ν M : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hM : 0 ≤ M)
    (F : ContinuousMap ℝ (TensorH3 c))
    (hF : ∀ r, ‖F r‖ ≤ M) :
    ContinuousAt (fun t => projectedHeatDuhamelIntegral (ν := ν) hc F t) 0 := by
  let K : ℝ := (M * ‖(UnforcedLeray.Train.toVecL :
    UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
    (4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  rw [Metric.continuousAt_iff]
  intro ε hε
  let δ : ℝ := (ε / (K + 1)) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hrootδ : Real.sqrt δ = ε / (K + 1) := by
    dsimp [δ]
    rw [Real.sqrt_sq (div_nonneg hε.le (by positivity))]
  refine ⟨δ, hδ, ?_⟩
  intro t hdist
  have htdist : |t| < δ := by
    simpa [Real.dist_eq] using hdist
  by_cases ht : 0 < t
  · have hbound := norm_projectedHeatDuhamelIntegral_le hc hν ht F
      (fun r hr => hF r)
    have htδ : t ≤ δ := le_of_lt (lt_of_le_of_lt (le_abs_self t) htdist)
    have hroot : t ^ (1 / 2 : ℝ) = Real.sqrt t := by
      rw [← Real.sqrt_eq_rpow]
    have hroot_t : Real.sqrt t ≤ Real.sqrt δ := Real.sqrt_le_sqrt htδ
    have hnorm : ‖projectedHeatDuhamelIntegral (ν := ν) hc F t‖ ≤ K * Real.sqrt t := by
      rw [hroot] at hbound
      dsimp [K]
      calc
        ‖projectedHeatDuhamelIntegral (ν := ν) hc F t‖ ≤
            (M * ‖(UnforcedLeray.Train.toVecL :
              UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
              ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * Real.sqrt t) := hbound
        _ = (M * ‖(UnforcedLeray.Train.toVecL :
              UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
              (4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ))) * Real.sqrt t := by ring
    have hsmall : K * Real.sqrt t < ε := by
      calc
        K * Real.sqrt t ≤ K * Real.sqrt δ := mul_le_mul_of_nonneg_left hroot_t hK
        _ = K * (ε / (K + 1)) := by rw [hrootδ]
        _ < ε := by
          have hfrac : K / (K + 1) < 1 := by
            rw [div_lt_one (by linarith : 0 < K + 1)]
            linarith
          have heps : 0 ≤ ε / (K + 1) := div_nonneg hε.le (by positivity)
          calc
            K * (ε / (K + 1)) = ε * (K / (K + 1)) := by ring
            _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
            _ = ε := by ring
    have hdistout : dist (projectedHeatDuhamelIntegral (ν := ν) hc F t)
        (projectedHeatDuhamelIntegral (ν := ν) hc F 0) < ε := by
      have hzero : projectedHeatDuhamelIntegral (ν := ν) hc F 0 = 0 := by
        simp [projectedHeatDuhamelIntegral]
      rw [hzero, dist_eq_norm, sub_zero]
      exact lt_of_le_of_lt hnorm hsmall
    exact hdistout
  · have htle : t ≤ 0 := le_of_not_gt ht
    have hzero_t : projectedHeatDuhamelIntegral (ν := ν) hc F t = 0 := by
      unfold projectedHeatDuhamelIntegral
      have hIoo : Ioo (0 : ℝ) t = ∅ := Ioo_eq_empty_of_le htle
      simp [hIoo]
    have hzero_0 : projectedHeatDuhamelIntegral (ν := ν) hc F 0 = 0 := by
      simp [projectedHeatDuhamelIntegral]
    rw [hzero_t, hzero_0]
    simp [dist_self]
    exact hε

#print axioms UnforcedLeray.TrainB.continuousAt_projectedHeatDuhamelIntegral_zero

end UnforcedLeray.TrainB
