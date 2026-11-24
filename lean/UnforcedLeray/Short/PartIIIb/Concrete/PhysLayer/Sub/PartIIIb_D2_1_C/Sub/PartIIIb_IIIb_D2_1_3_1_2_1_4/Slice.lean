import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Lap
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Select

/-!
# `adjDomGradSlice`: assembly

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
The slice Laplacian step `adjSliceLap` (`Slice/Lap.lean`) and the measurable periodic selection
`sliceSelect` (`Slice/Select/Select.lean`) feed `adjDomGradSlice_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- (a) Per-phase `H¹` regularity (source 1351-1362, 1470-1480). -/
theorem adjDomGradSlice : AdjDomGradSlice :=
  adjDomGradSlice_of adjSliceLap sliceSelect

end UnforcedLeray.Short.PartIIIb.Concrete
