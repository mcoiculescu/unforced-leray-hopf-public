import UnforcedLeray.Lib.TrainB.P0H3Operator
import UnforcedLeray.Lib.HeatCylinder.H3Operator
import UnforcedLeray.Lib.HeatCylinder.BochnerPath

/-!
# The actual projected Gaussian tensor map in cylinder H³

At every positive heat age, compose the proved Gaussian divergence response of the actual
row-oriented tensor with the actual cylinder Leray projection. This is the spatial operator in
the nonlinear Duhamel term; its singular coefficient is inherited from the Gaussian estimate.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

/-- The actual positive-age heat-divergence tensor map followed by the cylinder Leray projection.
-/
noncomputable def projectedHeatTensorBilinear {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) (hc1 : 1 ≤ c) :
    VectorH3 c → VectorH3 c → VectorH3 c :=
  fun u v => P0H3CLM hc (actualHeatDivH3Bilinear hc hθ hc1 u v)

/-- The Leray projection is contractive on the actual H³ graph. -/
theorem P0H3CLM_apply_norm_le {c : ℝ} (hc : 0 < c) (x : VectorH3 c) :
    ‖P0H3CLM hc x‖ ≤ ‖x‖ := by
  have hnorm : ‖(P0H3CLM hc : VectorH3 c →L[ℝ] VectorH3 c)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound
    · norm_num
    · intro y
      simpa [P0H3CLM] using P0H3Fun_norm_le hc y
  exact (P0H3CLM hc).le_opNorm x |>.trans
    (mul_le_of_le_one_left (norm_nonneg x) hnorm)

/-- Explicit positive-age bound for the actual projected tensor map. -/
theorem norm_projectedHeatTensorBilinear_apply_le {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) (hc1 : 1 ≤ c)
    (u v : VectorH3 c) :
    ‖projectedHeatTensorBilinear hc hθ hc1 u v‖ ≤
      ((ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff θ)).toReal) * 1536 * ‖u‖ * ‖v‖ := by
  change ‖P0H3CLM hc
      (actualHeatDivH3Bilinear hc hθ hc1 u v)‖ ≤ _
  exact (P0H3CLM_apply_norm_le hc _).trans
    (norm_actualHeatDivH3Bilinear_apply_le hc hθ hc1 u v)

/-- The coefficient multiplying the actual square-root time singularity, before integration. -/
def projectedHeatDuhamelConstant : ℝ :=
  1536 * ‖(UnforcedLeray.Train.toVecL :
    UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
    (2 / Real.sqrt Real.pi)

/-- On a positive age the projected tensor estimate has the explicit `age⁻¹ᐟ²` form. -/
theorem norm_projectedHeatTensorBilinear_age_bound {c ν τ : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hτ : 0 < τ) (hc1 : 1 ≤ c)
    (u v : VectorH3 c) :
    ‖projectedHeatTensorBilinear hc (mul_pos hν hτ) hc1 u v‖ ≤
      projectedHeatDuhamelConstant * ν ^ (-(1 / 2 : ℝ)) *
        τ ^ (-(1 / 2 : ℝ)) * ‖u‖ * ‖v‖ := by
  have hbase := norm_projectedHeatTensorBilinear_apply_le hc (mul_pos hν hτ) hc1 u v
  have hcoeff := heatDivL2Coeff_eq_singular hν hτ
  have hnorm : 0 ≤ ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ := norm_nonneg _
  have hcoeffpos : 0 ≤ heatDivL2Coeff (ν * τ) := by
    unfold heatDivL2Coeff
    positivity
  have hreal :
      (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff (ν * τ))).toReal =
        ‖(UnforcedLeray.Train.toVecL :
          UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
          heatDivL2Coeff (ν * τ) := by
    rw [← ENNReal.ofReal_mul hnorm]
    exact ENNReal.toReal_ofReal (mul_nonneg hnorm hcoeffpos)
  rw [hreal] at hbase
  dsimp [projectedHeatDuhamelConstant]
  have hνpow : 0 ≤ ν ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
  have hτpow : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ.le _
  have hnormu : 0 ≤ ‖u‖ := norm_nonneg _
  have hnormv : 0 ≤ ‖v‖ := norm_nonneg _
  rw [hcoeff] at hbase
  calc
    ‖projectedHeatTensorBilinear hc (mul_pos hν hτ) hc1 u v‖ ≤
        (‖(UnforcedLeray.Train.toVecL :
          UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
          ((2 / Real.sqrt Real.pi) *
            (ν ^ (-(1 / 2 : ℝ)) * τ ^ (-(1 / 2 : ℝ))))) * 1536 * ‖u‖ * ‖v‖ := hbase
    _ = projectedHeatDuhamelConstant * ν ^ (-(1 / 2 : ℝ)) *
          τ ^ (-(1 / 2 : ℝ)) * ‖u‖ * ‖v‖ := by
      dsimp [projectedHeatDuhamelConstant]
      ring

#print axioms UnforcedLeray.TrainB.P0H3CLM_apply_norm_le
#print axioms UnforcedLeray.TrainB.norm_projectedHeatTensorBilinear_apply_le
#print axioms UnforcedLeray.TrainB.norm_projectedHeatTensorBilinear_age_bound

end UnforcedLeray.TrainB
