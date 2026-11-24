import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_1_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.ActYDiff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanYDiff

/-!
# `PartIII-b:C/rep/8/1/1/2/3` (`yTermsDiff`): the four Y-terms are differentiable off the axis

Source `the November 2 reference manuscript` lines 4178-4186, 5400-5406, 5438-5448.

The actual terms (`actYDiff`, `PartIII-b:C/rep/8/1/1/2/3/1`) and the mean terms (`meanYDiff`,
`PartIII-b:C/rep/8/1/1/2/3/2`) give the two hypotheses of `yTermsDiff_of`, which splits the
four-term predicate `YTermsDiffAt` into its actual and mean halves.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3

/-- **`PartIII-b:C/rep/8/1/1/2/3`**: the four Y-terms are differentiable off the axis
(source 4178-4186, 5400-5406, 5438-5448). -/
theorem yTermsDiff (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.YTermsDiff :=
  yTermsDiff_of D (actYDiff D hst) (meanYDiff D hst)

end UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3
