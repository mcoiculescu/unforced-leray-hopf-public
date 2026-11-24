import UnforcedLeray.Lib.HeatCylinder.L2Operator
import UnforcedLeray.Lib.TrainB.VecBridge

/-!
# Train-vector form of the actual cylinder heat-divergence L² operator

This is the composition of the concrete B0296 quotient heatDiv operator and the train's
coordinate CLM. The normalized-cell measure and the `Plane`/`Vec` norm conversion remain explicit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

/-- The actual Gaussian heat-divergence operator with train-vector output on B0284's normalized
cell. -/
noncomputable def heatDivVecL2CLM {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c) →L[ℝ]
      Lp Vec 2 (UnforcedLeray.B0284.cellMeasure c) :=
  ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2
    (UnforcedLeray.B0284.cellMeasure c)).comp (heatDivL2CLM hc hθ)

@[simp] theorem heatDivVecL2CLM_apply {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : Lp (Plane × Plane) 2 (UnforcedLeray.B0284.cellMeasure c)) :
    heatDivVecL2CLM hc hθ x =
      ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2
        (UnforcedLeray.B0284.cellMeasure c)) (heatDivL2CLM hc hθ x) := rfl

/-- Explicit operator norm bound: the Gaussian coefficient `2 / sqrt(πθ)` times the coordinate
conversion norm from product-plane to Euclidean train vectors. -/
theorem norm_heatDivVecL2CLM_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    ‖heatDivVecL2CLM hc hθ‖ ≤
      ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ * heatDivL2Coeff θ := by
  have hcoeff : 0 ≤ heatDivL2Coeff θ := by
    unfold heatDivL2Coeff
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg _) hcoeff) fun x => ?_
  change ‖((UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2
    (UnforcedLeray.B0284.cellMeasure c)) (heatDivL2CLM hc hθ x)‖ ≤ _
  calc
    ‖((UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2
        (UnforcedLeray.B0284.cellMeasure c)) (heatDivL2CLM hc hθ x)‖ ≤
        ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2
          (UnforcedLeray.B0284.cellMeasure c)‖ * ‖heatDivL2CLM hc hθ x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2
          (UnforcedLeray.B0284.cellMeasure c)‖ *
        (heatDivL2Coeff θ * ‖x‖) := by
      gcongr
      exact heatDivL2CLM_norm_le hc hθ x
    _ ≤ ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        (heatDivL2Coeff θ * ‖x‖) := by
      gcongr
      exact ContinuousLinearMap.norm_compLpL_le _
    _ = (‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        heatDivL2Coeff θ) * ‖x‖ := by ring

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatDivVecL2CLM
#print axioms UnforcedLeray.HeatCylinder.norm_heatDivVecL2CLM_le
