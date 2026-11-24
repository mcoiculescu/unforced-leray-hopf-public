import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianShiftAverage
import UnforcedLeray.Lib.HeatCylinder.P0PlaneShift

/-!
# The actual Gaussian translation average preserves the Leray subspace

The average operator commutes with the centered-cell orthogonal Leray projection, because every
actual planar translation commutes with that projection and the Bochner integral is integrable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Cyl (L2v)
open UnforcedLeray.B0284 (heatKernel2)

/-- The Gaussian average of actual planar translations commutes with the actual centered-cell
Leray projection. -/
theorem centeredGaussianShiftAverageCLM_P0_comm {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (x : L2v c) :
    centeredGaussianShiftAverageCLM hc hθ (UnforcedLeray.Cyl.P0 c x) =
      UnforcedLeray.Cyl.P0 c (centeredGaussianShiftAverageCLM hc hθ x) := by
  rw [centeredGaussianShiftAverageCLM_apply, centeredGaussianShiftAverage,
    centeredGaussianShiftAverageCLM_apply, centeredGaussianShiftAverage]
  calc
    (∫ w : Plane, heatKernel2 θ w • planeShiftL2CLM hc w (UnforcedLeray.Cyl.P0 c x)) =
        ∫ w : Plane, (UnforcedLeray.Cyl.P0 c)
          (heatKernel2 θ w • planeShiftL2CLM hc w x) := by
            congr 1
            funext w
            rw [map_smul]
            change heatKernel2 θ w • planeShiftL2 hc w (UnforcedLeray.Cyl.P0 c x) = _
            rw [planeShiftL2_P0_comm hc w x, planeShiftL2CLM_apply]
    _ = UnforcedLeray.Cyl.P0 c
          (∫ w : Plane, heatKernel2 θ w • planeShiftL2CLM hc w x) :=
        (UnforcedLeray.Cyl.P0 c).integral_comp_comm
          (integrable_heatKernel2_smul_planeShiftL2CLM hc hθ x)

#print axioms UnforcedLeray.HeatCylinder.centeredGaussianShiftAverageCLM_P0_comm

end UnforcedLeray.HeatCylinder
