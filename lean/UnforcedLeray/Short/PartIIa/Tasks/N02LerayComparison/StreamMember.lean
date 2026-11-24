import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestFderiv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestAlgebra
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestOpK
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.BandIntegrable
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IbpQCell
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IbpEtaCell
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IbpKCell
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IntegralMeasureHCell
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.StreamMemLp
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.InnerCgradStream

/-!


Target: `NearStreamMember` (`Short/PartII-a/Sub/N02.lean`), source of record
`the November 2 reference manuscript`, lines 1730-1732.

Status: the unconditional proof of `NearStreamMember`, assembled from the proved assembly
`nearStreamMember_of` (`Sub/N02_2.lean`) and the ten leaf theorems in the folder
`Tasks/N02LerayComparison/StreamMember/`, each of which is compiled with zero `sorry`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem nearStreamMember_proof : UnforcedLeray.Short.PartIIa.NearStreamMember :=
  nearStreamMember_of cTestFderiv cTestAlgebra cTestOpK bandIntegrable ibpQCell ibpEtaCell
    ibpKCell integralMeasureHCell streamMemLp innerCgradStream

end UnforcedLeray.Short.PartIIa
