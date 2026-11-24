import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1.EarlyJet2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1.LateHeatDecomp2

/-!
# `PartIII-b:C/ward/12/3/2/2/1/2/1`: `RawResidualD2AxialTail`

Source of record:
`the November 2 reference manuscript`,
lines 1255-1304, 1310-1325, 2548-2551 at `k = 2`.

Assembles `rawResidualD2AxialTail : RawResidualD2AxialTail` from
`rawResidualD2AxialTail_of_early_and_late`, `resProfileEarlyJet2`, and `resProfileLateHeatDecomp2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Near-axis large-`|y 2|` second-derivative tail bound for the raw residual**
(`PartIII-b:C/ward/12/3/2/2/1/2/1`, `the November 2 reference manuscript`, lines 1270-1304, 1310-1325,
2548-2551). -/
theorem rawResidualD2AxialTail : RawResidualD2AxialTail :=
  rawResidualD2AxialTail_of_early_and_late resProfileEarlyJet2 resProfileLateHeatDecomp2

end UnforcedLeray.Short.PartIIIb.Concrete
