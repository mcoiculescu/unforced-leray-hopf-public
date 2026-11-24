import UnforcedLeray.Lib.HeatCylinder.HeatL2PlaneTranslation
import UnforcedLeray.Lib.TrainB.P0Horizontal

/-!
# The existing cylinder Leray projection commutes with full planar translations

The q and η shift lemmas compose to the actual two-coordinate translation used by the planar
Gaussian kernel.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Cyl (L2v)

/-- The centered-cell Leray projection commutes with the actual full planar translation. -/
theorem planeShiftL2_P0_comm {c : ℝ} (hc : 0 < c) (w : Plane) (x : L2v c) :
    planeShiftL2 hc w (UnforcedLeray.Cyl.P0 c x) =
      UnforcedLeray.Cyl.P0 c (planeShiftL2 hc w x) := by
  unfold planeShiftL2
  rw [UnforcedLeray.TrainB.etaShiftL2_P0_comm (a := -w.2)]
  rw [UnforcedLeray.TrainB.qShiftL2_P0_comm hc (a := -w.1)]

#print axioms UnforcedLeray.HeatCylinder.planeShiftL2_P0_comm

end UnforcedLeray.HeatCylinder
