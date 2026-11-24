import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_6_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.ApproxId.Formula
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.ApproxId.Integrable
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.ApproxId.Mass
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.ApproxId.Far

/-!
# `KerApproxId`: assembly from the four analytic leaves (SP 2081-2084, 3121)

The four leaves are `kerLapFormula`, `kerLapInt`, `kerLapMass` and `kerLapFar`, each proved in
its own file under `ApproxId/`.  The assembly `kerApproxId_of` is compiled in
`PartIII-a_T21_2_1_2_6_2.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem kerApproxId : UnforcedLeray.Short.IIIa.KerApproxId :=
  kerApproxId_of kerLapFormula kerLapInt kerLapMass kerLapFar

end UnforcedLeray.Short.IIIa
