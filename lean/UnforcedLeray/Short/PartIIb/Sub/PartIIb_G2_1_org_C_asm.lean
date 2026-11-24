import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C_3

/-!
# `PartII-b:G2/1/org/C`: `PhysKOutExistsBound`

Assembles `physKOutExistsBound_proof` from `physKOutExistsBound_of`, `physKOutCand`,
`physHpRep`, and `physKOutCongr`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem physKOutExistsBound_proof : PhysKOutExistsBound :=
  physKOutExistsBound_of physKOutCand physHpRep physKOutCongr

end UnforcedLeray.Short.IIb
