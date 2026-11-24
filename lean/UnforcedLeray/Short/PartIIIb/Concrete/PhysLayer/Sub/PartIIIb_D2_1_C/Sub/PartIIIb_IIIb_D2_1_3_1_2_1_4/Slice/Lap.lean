import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_1
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.sliceProdPairing
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.sliceDefectLocPer
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.periodicZero
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.sliceCountableTests

/-!
# `adjSliceLap`: assembly of the four leaves

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Combines `sliceProdPairing`, `sliceDefectLocPer`, `periodicZero` and `sliceCountableTests`
through `adjSliceLap_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem adjSliceLap : AdjSliceLap :=
  adjSliceLap_of sliceProdPairing sliceDefectLocPer periodicZero sliceCountableTests

end UnforcedLeray.Short.PartIIIb.Concrete
