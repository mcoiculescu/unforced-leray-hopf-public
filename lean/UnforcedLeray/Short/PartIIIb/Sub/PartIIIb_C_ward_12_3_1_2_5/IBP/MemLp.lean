import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1.CylMemLp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1.Meas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1.Envelope

/-!
# `inletFnMemLp` (assembly of the $L^{q_{0E}}$ membership for the inlet source)

Source `the November 2 reference manuscript`
lines 2542-2551, 2563-2569, 1206-1222.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem inletFnMemLp : InletFnMemLp :=
  inletFnMemLp_of cylProfile_memLp inletFnMeas inletFnEnvelope

end UnforcedLeray.Short.PartIIIb.Concrete
