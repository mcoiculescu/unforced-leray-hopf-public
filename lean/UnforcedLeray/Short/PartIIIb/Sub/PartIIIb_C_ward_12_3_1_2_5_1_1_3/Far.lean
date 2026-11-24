import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ProdHom
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.EFar
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.Drift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.RawFar

/-!
# `inletFnFarDecay` (assembly of far-field decay for the inlet source)

Source `the November 2 reference manuscript`
lines 2542-2548, 2563-2569, 1206-1222.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem inletFnFarDecay : InletFnFarDecay :=
  inletFnFarDecay_of_hom inletFnFarOfHom inletEFarHom inletDriftFar rawFarJets

end UnforcedLeray.Short.PartIIIb.Concrete
