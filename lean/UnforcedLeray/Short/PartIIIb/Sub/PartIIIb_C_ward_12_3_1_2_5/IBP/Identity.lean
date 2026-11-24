import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletFieldRegular
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletBackgroundBounds
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletL0Transpose
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletAdvTranspose1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletAdvTranspose2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletPairSplit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2.InletYIBP

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/2`: `InletIBPIdentity`

Source `the November 2 reference manuscript`
lines 2385-2387.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem inletIBPIdentity : InletIBPIdentity :=
  inletIBPIdentity_of inletBackgroundBounds
    (inletL0Transpose_of inletFieldRegular)
    (inletAdvTranspose1_of inletFieldRegular)
    (inletAdvTranspose2_of inletFieldRegular)
    (inletPairSplit_of inletFieldRegular)
    (inletYIBP_of inletFieldRegular)

end UnforcedLeray.Short.PartIIIb.Concrete
