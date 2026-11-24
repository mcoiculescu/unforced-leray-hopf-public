import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockB1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockB3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockA1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockB2

/-!
# Leaf 2 (`PartIII-b:C/ward/12/3/2/2/1/2/1/2`): `ResProfileLateHeatDecomp2`

Source of record: `the November 2 reference manuscript`,
lines 247-258, 447-459 (`sct:expansion`), 1255-1285, 1310-1325, 2548-2551.

Assembles `resProfileLateHeatDecomp2 : ResProfileLateHeatDecomp2` from `resProfileLateHeatDecomp2_of_blocks`
and the four mean-block heat-split theorems `meanBlockB1LateHeatSplit2`, `meanBlockB3LateHeatSplit2`,
`meanBlockA1LateHeatSplit2`, `meanBlockB2LateHeatSplit2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Late-age (`s ≥ 1`) finite-order heat decomposition of the lifted residual**
(`PartIII-b:C/ward/12/3/2/2/1/2/1/2`, `the November 2 reference manuscript`, lines 1267-1285, 1310-1325, 2548-2551). -/
theorem resProfileLateHeatDecomp2 : ResProfileLateHeatDecomp2 :=
  resProfileLateHeatDecomp2_of_blocks
    meanBlockB1LateHeatSplit2
    meanBlockB3LateHeatSplit2
    meanBlockA1LateHeatSplit2
    meanBlockB2LateHeatSplit2

end UnforcedLeray.Short.PartIIIb.Concrete
