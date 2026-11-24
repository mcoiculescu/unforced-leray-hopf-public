import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Formula
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.S
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.A
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.C

/-!
# `RingChartRawD2` (`PartIII-b:C/rep/8/2/1/3`, assembly)

Source `the November 2 reference manuscript`
lines 5460-5463.  Assembles the accepted `rawProfileSmooth`, `axisExtPd`, `chartId` with the
formula `ringFrameD2Formula` (`…/3/a`) and the bound `ringFrameD2Bound` (`…/3/b`) through
`ringChartRawD2_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ringChartRawD2 : RingChartRawD2 :=
  ringChartRawD2_of rawProfileSmooth axisExtPd chartId ringFrameD2Formula ringFrameD2Bound

end UnforcedLeray.Short.PartIIIb.Concrete
