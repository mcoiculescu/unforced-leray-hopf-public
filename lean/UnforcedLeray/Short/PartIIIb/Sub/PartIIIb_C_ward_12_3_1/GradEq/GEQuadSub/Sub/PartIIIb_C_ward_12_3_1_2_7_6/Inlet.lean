import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L5

/-!
# `GEQInletGlobal` (assembly)

Source `the November 2 reference manuscript`
lines 2562-2564, 2385-2387. Direct application of `gEQInletGlobal_of` to the five accepted
lemmas `inletProfGlobal`, `nvFirstPt`, `nvSecondPt`, `majLp`, `nvBdd`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gEQInletGlobal : GEQInletGlobal :=
  gEQInletGlobal_of inletProfGlobal nvFirstPt nvSecondPt majLp nvBdd

end UnforcedLeray.Short.PartIIIb.Concrete
