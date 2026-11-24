import UnforcedLeray.Lib.TrainB.P0CompactNonlinearContraction

/-!
# Compact-time ball bound for the actual nonlinear Duhamel operator

On the same half-contraction time interval, the nonlinear Duhamel output lies in the smaller
radius-`R/4` ball. This is the nonlinear contribution to the eventual affine mild self-map.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- The actual compact-time nonlinear Duhamel map sends the radius-`R` H³ ball into the
radius-`R/4` ball when its explicit Lipschitz coefficient is at most one half. -/
theorem norm_projectedNonlinearDuhamelCompactMap_le_quarter {c ν T R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T) (hR : 0 ≤ R)
    (hsmall : projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ) ≤ 1 / 2)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) (hu : ‖u‖ ≤ R) :
    ‖projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u‖ ≤ R / 4 := by
  have hR4 : 0 ≤ R / 4 := by positivity
  rw [ContinuousMap.norm_le _ hR4]
  intro t
  have hpoint := norm_projectedNonlinearDuhamelCompactMap_apply_le hc hc1 hν hT.le
    u hu t
  have halgebra :
      (1536 * R ^ 2 * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
        ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ)) =
      (R / 2) * (projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ)) := by
    unfold projectedHeatNonlinearityLipschitzCoeff
    ring
  rw [halgebra] at hpoint
  calc
    ‖projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t‖ ≤
        (R / 2) * (projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ)) := hpoint
    _ ≤ R / 4 := by
      calc
        _ ≤ (R / 2) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ = R / 4 := by ring

#print axioms UnforcedLeray.TrainB.norm_projectedNonlinearDuhamelCompactMap_le_quarter

end UnforcedLeray.TrainB
