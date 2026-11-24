import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3.ShiftRep
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3.ParamInt
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3.LapCellTest

/-!
# Part I, leaf `PartI:T02/1/4/6/4/2/3` (`LeafShiftLapCH`), proof

Source of record: `the November 2 reference manuscript`.

Assembles `LeafShiftLapCH` from the three leaves `leafShiftRepCH_proof`,
`leafParamIntCH_proof` and `leafLapCellTestCH_proof` via `leafShiftLapCH_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem leafShiftLapCH_proof : UnforcedLeray.Short.PartI.LeafShiftLapCH :=
  leafShiftLapCH_of leafShiftRepCH_proof leafParamIntCH_proof leafLapCellTestCH_proof

end UnforcedLeray.Short.PartI
