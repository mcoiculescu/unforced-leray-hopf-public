import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.S
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.A
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.C
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.N0
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.N1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.N2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.B0
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.B1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.B2

/-!
# `RingChartRawD1` from the nine leaf facts (`PartIII-b:C/rep/8/2/1/2`)

Assembly of `ringChartRawD1_of` with the leaf proofs `rawProfileSmooth` (S), `axisExtPd` (A),
`chartId` (C), `nvPd0`, `nvPd1`, `nvPd2` (N0, N1, N2), and `rawD1Bound0`, `rawD1Bound1`,
`rawD1Bound2` (B0, B1, B2).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `RingChartRawD1` holds: the first-derivative ring-chart bound, assembled from the nine leaves. -/
theorem ringChartRawD1 : RingChartRawD1 :=
  ringChartRawD1_of rawProfileSmooth axisExtPd chartId nvPd0 nvPd1 nvPd2
    rawD1Bound0 rawD1Bound1 rawD1Bound2

end UnforcedLeray.Short.PartIIIb.Concrete
