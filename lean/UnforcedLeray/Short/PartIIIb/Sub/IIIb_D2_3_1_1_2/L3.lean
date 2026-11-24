import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# `sepPhiMeasurable` (`PartIII-b:IIIb-D2/3/1/1/2/3`)

Source `the November 2 reference manuscript`
3604-3621 (`sep:kernel`, `sep:resolvent`).  Unconditional assembly of the measurability input
`SepPhiMeasurable`: the heat-Leray scaling (from `heatGTailScale`), the joint measurability
`HeatLerayJointMeas` and the smoothness `HeatLerayKSmooth` feed `sepPhiMeasurable_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepPhiMeasurable : SepPhiMeasurable :=
  sepPhiMeasurable_of (heatLerayJointMeas_of (heatLerayScale_of heatGTailScale) heatLerayKSmooth)
    heatLerayKSmooth

end UnforcedLeray.Short.PartIIIb.Concrete
