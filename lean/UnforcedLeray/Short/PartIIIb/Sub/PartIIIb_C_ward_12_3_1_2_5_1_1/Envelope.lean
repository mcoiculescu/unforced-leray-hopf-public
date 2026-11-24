import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3.Far
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3.Near

/-!
# `inletFnEnvelope` (assembly of the cylindrical envelope for the inlet source)

Source `the November 2 reference manuscript`
lines 2542-2551, 2563-2569, 1206-1222.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem inletFnEnvelope : InletFnEnvelope :=
  inletFnEnvelope_of inletFnFarDecay inletFnNearBound

end UnforcedLeray.Short.PartIIIb.Concrete
