import UnforcedLeray.Lib.Train.Ops
import UnforcedLeray.Units.B0284.Defs

/-!
# Coordinate bridge from the train's Euclidean vectors to the heat-kernel plane fields

The train evolution uses `Train.Vec = EuclideanSpace ℝ (Fin 2)`, while the explicit heat-divergence
kernel is written for `Plane = ℝ × ℝ`. This module provides the inverse coordinate map and its
periodicity bridge. Norms and cell measures are intentionally kept explicit for subsequent
comparison lemmas.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.TrainB

open UnforcedLeray.Train (Vec)
open UnforcedLeray.GaussianVortex (Plane)
open MeasureTheory
open scoped ENNReal

/-- Read a train vector as its two Cartesian components in the product plane. -/
def planeOfVec (u : Vec) : Plane := (u 0, u 1)

@[simp] theorem toVec_planeOfVec (u : Vec) : UnforcedLeray.Train.toVec (planeOfVec u) = u := by
  simpa [planeOfVec] using (UnforcedLeray.Train.eq_toVec u).symm

@[simp] theorem planeOfVec_toVec (z : Plane) :
    planeOfVec (UnforcedLeray.Train.toVec z) = z := by
  ext <;> simp [planeOfVec]

/-- The component map is the inverse coordinate equivalence, so its max-norm loss is bounded
by the operator norm of `toVecL.symm`. -/
theorem planeOfVec_eq_toVecL_symm (u : Vec) :
    planeOfVec u = UnforcedLeray.Train.toVecL.symm u := by
  apply UnforcedLeray.Train.toVec_injective
  calc UnforcedLeray.Train.toVec (planeOfVec u) = u := toVec_planeOfVec u
    _ = UnforcedLeray.Train.toVecL (UnforcedLeray.Train.toVecL.symm u) :=
      (UnforcedLeray.Train.toVecL.apply_symm_apply u).symm

theorem norm_planeOfVec_le (u : Vec) :
    ‖planeOfVec u‖ ≤ ‖(UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane)‖ * ‖u‖ := by
  rw [planeOfVec_eq_toVecL_symm]
  exact ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).le_opNorm u)

/-- Reverse norm comparison for representing a product-plane field as the train's Euclidean
vector. -/
theorem norm_toVec_le (z : Plane) :
    ‖UnforcedLeray.Train.toVec z‖ ≤ ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ * ‖z‖ :=
  (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).le_opNorm z

/-- Coordinatewise product-plane representative of a train velocity field. -/
def planeFieldOfVec (u : Plane → Vec) : Plane → Plane := fun z => planeOfVec (u z)

/-- Coordinatewise train-vector representative of a product-plane field. -/
def vecFieldOfPlane (u : Plane → Plane) : Plane → Vec := fun z => UnforcedLeray.Train.toVec (u z)

/-- The coordinate bridge transfers every cylinder-cell `L^p` norm with the explicit linear
equivalence constant. -/
theorem eLpNorm_planeFieldOfVec_le {c : ℝ} {p : ℝ≥0∞} {u : Plane → Vec} :
    eLpNorm (planeFieldOfVec u) p (UnforcedLeray.B0284.cellMeasure c) ≤
      ENNReal.ofReal (‖(UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane)‖) *
        eLpNorm u p (UnforcedLeray.B0284.cellMeasure c) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ p
  filter_upwards with z
  exact norm_planeOfVec_le (u z)

/-- The reverse coordinate transfer also keeps its explicit equivalence constant. -/
theorem eLpNorm_vecFieldOfPlane_le {c : ℝ} {p : ℝ≥0∞} {u : Plane → Plane} :
    eLpNorm (vecFieldOfPlane u) p (UnforcedLeray.B0284.cellMeasure c) ≤
      ENNReal.ofReal (‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖) *
        eLpNorm u p (UnforcedLeray.B0284.cellMeasure c) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ p
  filter_upwards with z
  exact norm_toVec_le (u z)

/-- Measurability transfers through the continuous coordinate equivalence. -/
theorem aestronglyMeasurable_planeFieldOfVec {u : Plane → Vec}
    (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (planeFieldOfVec u) volume := by
  have hcont : Continuous planeOfVec :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).continuous
  exact hcont.comp_aestronglyMeasurable hu

/-- Measurability transfers from product-plane fields to train-vector fields. -/
theorem aestronglyMeasurable_vecFieldOfPlane {u : Plane → Plane}
    (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (vecFieldOfPlane u) volume := by
  have hcont : Continuous UnforcedLeray.Train.toVec :=
    (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).continuous
  exact hcont.comp_aestronglyMeasurable hu

/-- The vector-to-plane bridge preserves the exact periodicity condition used by B0284. -/
theorem periodic_planeFieldOfVec {c : ℝ} {u : Plane → Vec}
    (hu : UnforcedLeray.Cyl.IsPeriodic c u) :
    UnforcedLeray.B0284.IsQPeriodic c (planeFieldOfVec u) := by
  intro z
  simp [planeFieldOfVec, hu z]

/-- Conversely, the coordinate map lifts a periodic product-plane field to a periodic train
vector field. -/
theorem periodic_vecFieldOfPlane {c : ℝ} {u : Plane → Plane}
    (hu : UnforcedLeray.B0284.IsQPeriodic c u) :
    UnforcedLeray.Cyl.IsPeriodic c (vecFieldOfPlane u) := by
  intro z
  simp [vecFieldOfPlane, hu z]

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.toVec_planeOfVec
#print axioms UnforcedLeray.TrainB.periodic_planeFieldOfVec
#print axioms UnforcedLeray.TrainB.norm_planeOfVec_le
#print axioms UnforcedLeray.TrainB.norm_toVec_le
