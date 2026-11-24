import UnforcedLeray.Lib.TrainB.P0CompactNonlinearDuhamel
import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelLipschitz

/-!
# Compact-time Lipschitz bound for the actual nonlinear Duhamel map

The full-line Lipschitz estimate transfers to compact-time trajectories through the same
constant-at-the-ends extension used in the definition of the operator.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

private theorem norm_neg_sub_neg {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖-x - -y‖ = ‖x - y‖ := by
  calc
    ‖-x - -y‖ = ‖-(x - y)‖ := by
      congr 1
      simp [sub_eq_add_neg]
      abel
    _ = ‖x - y‖ := norm_neg _

/-- Pointwise Lipschitz bound for the compact-time nonlinear Duhamel map on a uniform H³ ball. -/
theorem norm_projectedNonlinearDuhamelCompactMap_sub_le {c ν T R δ : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (u v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (huv : ‖u - v‖ ≤ δ)
    (t : Icc (0 : ℝ) T) :
    ‖projectedNonlinearDuhamelCompactMap hc hc1 hν hT u t -
      projectedNonlinearDuhamelCompactMap hc hc1 hν hT v t‖ ≤
      ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
        ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ)) := by
  let uext : ContinuousMap ℝ (VectorH3 c) := extendCompactPath hT u
  let vext : ContinuousMap ℝ (VectorH3 c) := extendCompactPath hT v
  by_cases hzero : (t : ℝ) = 0
  · have hu0 : projectedNonlinearDuhamelCompactMap hc hc1 hν hT u t = 0 := by
      rw [projectedNonlinearDuhamelCompactMap_apply]
      rw [hzero]
      simp [projectedHeatNonlinearityIntegral, projectedHeatDuhamelOrbit]
    have hv0 : projectedNonlinearDuhamelCompactMap hc hc1 hν hT v t = 0 := by
      rw [projectedNonlinearDuhamelCompactMap_apply]
      rw [hzero]
      simp [projectedHeatNonlinearityIntegral, projectedHeatDuhamelOrbit]
    rw [hu0, hv0]
    simp only [sub_self, norm_zero]
    positivity
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm hzero)
    have hboundU : ∀ r ∈ Ioo (0 : ℝ) (t : ℝ), ‖uext r‖ ≤ R := by
      intro r hr
      exact le_trans (norm_extendCompactPath_le hT u r) hu
    have hboundV : ∀ r ∈ Ioo (0 : ℝ) (t : ℝ), ‖vext r‖ ≤ R := by
      intro r hr
      exact le_trans (norm_extendCompactPath_le hT v r) hv
    have hboundSub : ∀ r ∈ Ioo (0 : ℝ) (t : ℝ), ‖uext r - vext r‖ ≤ δ := by
      intro r hr
      change ‖u (clampTimeMap T hT r) - v (clampTimeMap T hT r)‖ ≤ δ
      calc
        ‖u (clampTimeMap T hT r) - v (clampTimeMap T hT r)‖ =
            ‖(u - v) (clampTimeMap T hT r)‖ := by simp
        _ ≤ ‖u - v‖ := (u - v).norm_coe_le_norm (clampTimeMap T hT r)
        _ ≤ δ := huv
    have hnonlin := norm_projectedHeatNonlinearityIntegral_sub_le hc hν htpos hc1
      uext vext hR hboundU hboundV hboundSub
    rw [projectedNonlinearDuhamelCompactMap_apply,
      projectedNonlinearDuhamelCompactMap_apply]
    have htime : (t : ℝ) ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow t.2.1 t.2.2 (by norm_num)
    have hpositive :
        ‖projectedHeatNonlinearityIntegral (ν := ν) hc hc1 uext (t : ℝ) -
            projectedHeatNonlinearityIntegral (ν := ν) hc hc1 vext (t : ℝ)‖ ≤
          ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
            UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
            ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ)) := by
      calc
        ‖projectedHeatNonlinearityIntegral (ν := ν) hc hc1 uext (t : ℝ) -
            projectedHeatNonlinearityIntegral (ν := ν) hc hc1 vext (t : ℝ)‖ ≤
            ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
              UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
              ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * (t : ℝ) ^ (1 / 2 : ℝ)) :=
          hnonlin
        _ ≤ ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
              UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
              ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left htime (by positivity)
    rw [norm_neg_sub_neg]
    exact hpositive

#print axioms UnforcedLeray.TrainB.norm_projectedNonlinearDuhamelCompactMap_sub_le

end UnforcedLeray.TrainB
