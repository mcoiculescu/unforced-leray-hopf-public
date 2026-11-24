import UnforcedLeray.Lib.HeatCylinder.HeatL2SemigroupClosed
import UnforcedLeray.Lib.TrainB.VecBridge

/-!
# The actual zero-order cylinder heat on Train's Euclidean vector carrier

This is the B0284 Gaussian heat quotient conjugated through the genuine coordinate equivalence
between `Plane` and `Train.Vec`. The two finite-dimensional operator norms are retained explicitly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

/-- The actual B0284 Gaussian heat on normalized-cell Euclidean vector-valued `L²`, obtained by
conjugating `heatL2CLM` through Train's coordinate equivalence. -/
def heatVecL2CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    Lp Vec 2 (cellMeasure c) →L[ℝ] Lp Vec 2 (cellMeasure c) :=
  ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)).comp
    ((heatL2CLM hc θ).comp
      ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c)))

/-- The actual Plane heat quotient is contractive at every age. -/
theorem norm_heatL2CLM_le_one {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    ‖heatL2CLM hc θ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [heatL2CLM_apply]
  simpa using norm_heatL2_le hc x

/-- Unfolding the conjugated operator shows its actual normalized-cell quotient action. -/
theorem heatVecL2CLM_apply {c : ℝ} (hc : 0 < c) (θ : ℝ)
    (x : Lp Vec 2 (cellMeasure c)) :
    heatVecL2CLM hc θ x =
      (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)
        (heatL2CLM hc θ
          ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2
            (cellMeasure c) x)) := rfl

/-- Operator norm bound for the vector-carrier heat, with both coordinate factors visible. -/
theorem norm_heatVecL2CLM_le {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    ‖heatVecL2CLM hc θ‖ ≤
      ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)‖ *
      ‖heatL2CLM hc θ‖ *
      ‖(UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c)‖ := by
  calc
    ‖heatVecL2CLM hc θ‖ ≤
        ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)‖ *
          ‖(heatL2CLM hc θ).comp
            ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2
              (cellMeasure c))‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _)

/-- The vector-carrier heat has a period-independent bound; only the explicit coordinate
norms remain. -/
theorem norm_heatVecL2CLM_le_coordinates {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    ‖heatVecL2CLM hc θ‖ ≤
      ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
      ‖(UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane)‖ := by
  let A : Lp Plane 2 (cellMeasure c) →L[ℝ] Lp Vec 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)
  let C : Lp Vec 2 (cellMeasure c) →L[ℝ] Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c)
  have hA : ‖A‖ ≤ ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ := by
    exact ContinuousLinearMap.norm_compLpL_le _
  have hC : ‖C‖ ≤ ‖(UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane)‖ := by
    exact ContinuousLinearMap.norm_compLpL_le _
  have hH : ‖heatL2CLM hc θ‖ ≤ 1 := norm_heatL2CLM_le_one hc θ
  change ‖A.comp ((heatL2CLM hc θ).comp C)‖ ≤ _
  calc
    ‖A.comp ((heatL2CLM hc θ).comp C)‖ ≤ ‖A‖ * ‖heatL2CLM hc θ‖ * ‖C‖ := by
      calc
        _ ≤ ‖A‖ * ‖(heatL2CLM hc θ).comp C‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖A‖ * (‖heatL2CLM hc θ‖ * ‖C‖) := by
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _)
        _ = _ := by ring
    _ ≤ ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        ‖(UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane)‖ := by
      have hnonneg : 0 ≤ ‖C‖ := norm_nonneg _
      have hstep1 : ‖A‖ * ‖heatL2CLM hc θ‖ * ‖C‖ ≤ ‖A‖ * 1 * ‖C‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hH (norm_nonneg _)) hnonneg
      have hstep2 : ‖A‖ * 1 * ‖C‖ ≤
          ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
            ‖(UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane)‖ := by
        simpa using mul_le_mul hA hC (norm_nonneg _) (norm_nonneg _)
      exact hstep1.trans hstep2

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecL2CLM_apply
#print axioms UnforcedLeray.HeatCylinder.norm_heatL2CLM_le_one
#print axioms UnforcedLeray.HeatCylinder.norm_heatVecL2CLM_le
#print axioms UnforcedLeray.HeatCylinder.norm_heatVecL2CLM_le_coordinates
