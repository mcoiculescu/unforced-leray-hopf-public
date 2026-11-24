import UnforcedLeray.Lib.TrainB.P0CompactNonlinearDuhamelLipschitz
import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelTimeChoice

/-!
# Short-time contraction for the actual compact nonlinear Duhamel operator

The compact-time Lipschitz estimate is exactly the coefficient selected by the square-root-kernel
time choice. This packages the half-contraction statement on the uniform H³ ball.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- A short interval makes the actual nonlinear compact Duhamel map a contraction on an H³ ball. -/
theorem norm_projectedNonlinearDuhamelCompactMap_sub_le_half {c ν T R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T) (hR : 0 ≤ R)
    (hsmall : projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ) ≤ 1 / 2)
    (u v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u -
      projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v‖ ≤
      (1 / 2 : ℝ) * ‖u - v‖ := by
  have hhalf : 0 ≤ (1 / 2 : ℝ) * ‖u - v‖ := by positivity
  rw [ContinuousMap.norm_le _ hhalf]
  intro t
  have hpoint := norm_projectedNonlinearDuhamelCompactMap_sub_le hc hc1 hν hT.le
    hR (norm_nonneg (u - v)) u v hu hv le_rfl t
  calc
    ‖projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t -
        projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v t‖ ≤
        ((3072 * R * ‖u - v‖) * ‖(UnforcedLeray.Train.toVecL :
          UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
          ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ)) := hpoint
    _ = (projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ)) *
          ‖u - v‖ := by
        simp [projectedHeatNonlinearityLipschitzCoeff]
        ring
    _ ≤ (1 / 2 : ℝ) * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)

/-- The explicit time-selection theorem supplies a positive compact interval for the preceding
half-contraction estimate. -/
theorem exists_compact_nonlinear_half_contraction_time {ν R : ℝ}
    (hν : 0 < ν) (hR : 0 ≤ R) :
    ∃ T : ℝ, 0 < T ∧
      projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ) ≤ 1 / 2 :=
  exists_train_short_contraction_time hν hR

#print axioms UnforcedLeray.TrainB.norm_projectedNonlinearDuhamelCompactMap_sub_le_half
#print axioms UnforcedLeray.TrainB.exists_compact_nonlinear_half_contraction_time

end UnforcedLeray.TrainB
