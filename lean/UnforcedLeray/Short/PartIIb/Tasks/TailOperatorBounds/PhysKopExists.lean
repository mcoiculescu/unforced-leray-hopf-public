import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_B1_reg
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_A
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_B2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C_asm
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_D
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds.PhysKOutLinComb

/-!
# `PartII-b:G2/1`: `PhysKopExists`

Source of record: `the November 2 reference manuscript`, lines 2007–2010, 2432–2437.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem physKopExists_proof : PhysKopExists :=
  physKopExists_of_smooth physRespLinComb_proof physKOutLinCombSmooth_proof physKOutUnique
    physKOutExistsBound_proof physRespReal

end UnforcedLeray.Short.IIb
