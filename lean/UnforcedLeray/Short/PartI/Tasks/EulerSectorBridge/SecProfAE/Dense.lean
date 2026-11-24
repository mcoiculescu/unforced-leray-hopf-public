import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_2
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.Dense.SectorSumsL2

/-!
# Part I, task `PartI:S11/1/2`: `smoothSectorSumsDense`

Source of record: `the November 2 reference manuscript`, lines 841-889.
Proof: the density in `L²_M` of the finite smooth sector sums (`smoothSectorSumsDenseL2_proof`,
leaf `PartI:S11/1/2/2`) transports to the density in `H^0_M` (`smoothSectorSumsDense_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Short.PartI

theorem smoothSectorSumsDense : SmoothSectorSumsDense :=
  smoothSectorSumsDense_of smoothSectorSumsDenseL2_proof

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.smoothSectorSumsDense
