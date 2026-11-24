import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2.ProdConv
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2.SmoothSeq

/-!
# Part I, task `PartI:T02/1/2/3/1/2`: smooth approximation for the cylinder Leibniz rule

Source of record: `the November 2 reference manuscript`, lines 261-288.

Proves `BdpSmoothApprox` by applying `bdp_smoothApprox_of` to the two leaves
`bdp_prodConv` (`PartI:T02/1/2/3/1/2/1`) and `bdp_smoothSeq` (`PartI:T02/1/2/3/1/2/2`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

theorem bdp_smoothApprox : UnforcedLeray.Short.PartI.BdpSmoothApprox :=
  bdp_smoothApprox_of bdp_prodConv bdp_smoothSeq

end UnforcedLeray.Short.PartI
