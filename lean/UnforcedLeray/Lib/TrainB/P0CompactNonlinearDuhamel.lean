import UnforcedLeray.Lib.TrainB.P0CompactPathExtension
import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelEstimate

/-!
# The actual nonlinear Duhamel map on a compact time interval

For a compact-time H³ path, extend it constantly at the endpoints, form the literal row tensor,
and apply the actual projected Gaussian Duhamel integral. The preceding leaves provide continuity
and the global stress bound needed by that integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

/-- Inclusion of the compact time interval into the real line. -/
def compactTimeInclusion {T : ℝ} : ContinuousMap (Icc (0 : ℝ) T) ℝ :=
  ⟨fun t => t, continuous_subtype_val⟩

/-- The negative actual projected Gaussian nonlinear Duhamel map, giving the Navier–Stokes mild sign. -/
def projectedNonlinearDuhamelCompactMap {c ν T : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 ≤ T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) :
    ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) := by
  let uext : ContinuousMap ℝ (VectorH3 c) := extendCompactPath hT u
  let F : ContinuousMap ℝ (TensorH3 c) := tensorH3StressPath hc1 uext
  let M : ℝ := 1536 * ‖u‖ ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hF : ∀ r, ‖F r‖ ≤ M := by
    intro r
    dsimp [F, M]
    exact norm_tensorH3StressPath_extendCompactPath_le hc1 hT u r
  exact -((projectedHeatDuhamelContinuousMap hc hν hM F hF).comp compactTimeInclusion)

@[simp]
theorem projectedNonlinearDuhamelCompactMap_apply {c ν T : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 ≤ T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) (t : Icc (0 : ℝ) T) :
    projectedNonlinearDuhamelCompactMap hc hc1 hν hT u t =
      -projectedHeatNonlinearityIntegral (ν := ν) hc hc1
        (extendCompactPath hT u) t := rfl

/-- The nonlinear Duhamel map sends a radius-`R` compact-time path to a path whose norm is bounded
by the explicit square-root-time estimate. -/
theorem norm_projectedNonlinearDuhamelCompactMap_apply_le {c ν T R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 ≤ T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) (hball : ‖u‖ ≤ R)
    (t : Icc (0 : ℝ) T) :
    ‖projectedNonlinearDuhamelCompactMap hc hc1 hν hT u t‖ ≤
      (1536 * R ^ 2 * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
        ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ)) := by
  have hnorm : ‖u t‖ ≤ R := le_trans (u.norm_coe_le_norm t) hball
  by_cases ht : (t : ℝ) = 0
  · have hzero : projectedHeatNonlinearityIntegral (ν := ν) hc hc1
        (extendCompactPath hT u) (t : ℝ) = 0 := by
      rw [ht]
      simp [projectedHeatNonlinearityIntegral, projectedHeatDuhamelOrbit]
    rw [projectedNonlinearDuhamelCompactMap_apply, hzero]
    simp only [norm_neg, norm_zero]
    positivity
  · have htpos : 0 < (t : ℝ) := by
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      exact lt_of_le_of_ne ht0 (Ne.symm ht)
    have hbound : ∀ r ∈ Ioo (0 : ℝ) (t : ℝ),
        ‖extendCompactPath hT u r‖ ≤ R := by
      intro r hr
      exact le_trans (norm_extendCompactPath_le hT u r) hball
    have hnonlin := norm_projectedHeatNonlinearityIntegral_le hc hν htpos hc1
      (extendCompactPath hT u) hbound
    rw [projectedNonlinearDuhamelCompactMap_apply, norm_neg]
    have htime : (t : ℝ) ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow (by positivity) t.2.2 (by norm_num)
    have hcoeff : 0 ≤ (1536 * R ^ 2 * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
        ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ))) := by positivity
    calc
      ‖projectedHeatNonlinearityIntegral (ν := ν) hc hc1
          (extendCompactPath hT u) (t : ℝ)‖ ≤
          (1536 * R ^ 2 * ‖(UnforcedLeray.Train.toVecL :
            UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
            ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * (t : ℝ) ^ (1 / 2 : ℝ)) := by
              refine hnonlin.trans ?_
              gcongr
      _ ≤ (1536 * R ^ 2 * ‖(UnforcedLeray.Train.toVecL :
            UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
            ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left htime (by positivity)

#print axioms UnforcedLeray.TrainB.projectedNonlinearDuhamelCompactMap
#print axioms UnforcedLeray.TrainB.norm_projectedNonlinearDuhamelCompactMap_apply_le

end UnforcedLeray.TrainB
