import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1.ExistsApproxId
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1.SpatMolMemLoc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1.SpatMolSliceSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1.DySSpatMolAe

/-!
# Weak product rule in `y`

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`), phase tests 2525-2531.
Assembled by `weakMulRule_of` from the approximate identity, `MemLpLoc` stability of the spatial
mollification, smoothness of a.e. mollified slice, and the a.e. slice derivative identity.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem weakMulRule : WeakMulRule :=
  weakMulRule_of exists_approxId spatMol_memLoc spatMol_sliceSmooth dyS_spatMol_ae

end UnforcedLeray.Short.PartIIIb.Concrete
