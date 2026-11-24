import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2.SmoothSeq_Sub
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2.SmoothFun
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2.ValueBound
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2.DerivConv

/-!
# Part I, task `PartI:T02/1/2/3/1/2/2`: smooth periodic approximants

Source of record: `the November 2 reference manuscript`, lines 261-288.

Assembles `BdpSmoothSeq` from the three leaves `bdp_smoothFun`, `bdp_valueBound`,
`bdp_derivConv` through `bdp_smoothSeq_of` (in `SmoothSeq_Sub.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

theorem bdp_smoothSeq : UnforcedLeray.Short.PartI.BdpSmoothSeq :=
  bdp_smoothSeq_of bdp_smoothFun bdp_valueBound bdp_derivConv

end UnforcedLeray.Short.PartI
