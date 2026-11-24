import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_2.SqLap
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIBPLeaves.FmrIBPDiff.GreenCut
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIBPLeaves.FmrIBPDiff.Limit

/-!
# Leaf `PartIII-a:T21/c2/2/5/2` (`fmrIBPDiff`): assembly of `FmrIBPDiff`

Source: `the November 2 reference manuscript` lines 2950-2954.
Combines `diffGreenCut`, `diffSqLap` and `diffLimit` through `fmrIBPDiff_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem fmrIBPDiff : FmrIBPDiff :=
  fmrIBPDiff_of diffGreenCut diffSqLap diffLimit

end UnforcedLeray.Short.IIIa
