import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_6.Holder
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_6.Inlet

/-!
# `GEQYq` (assembly)

Source `the November 2 reference manuscript`
lines 2562-2564, 2385-2387, 1515-1531.  Direct application of `gEQYq_of` to
`gEQFieldCell_of_inlet` (Holder, accepted) applied to `gEQInletGlobal` (Inlet, accepted).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gEQYq : GEQYq :=
  gEQYq_of (gEQFieldCell_of_inlet gEQInletGlobal)

end UnforcedLeray.Short.PartIIIb.Concrete
