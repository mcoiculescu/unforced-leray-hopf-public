import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_2

/-!
# `PartII-a:F09/2`: adjoint maximal domain

Final assembly: the reversed window estimate (proved unconditionally as
`adjointLocalWindowEstimate_viaForward`) feeds `adjointMaximalDomain_of`, giving the
adjoint maximal domain statement `AdjointMaximalDomain`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem adjointMaximalDomain : AdjointMaximalDomain :=
  adjointMaximalDomain_of adjointLocalWindowEstimate_viaForward

end UnforcedLeray.Short.PartIIa
