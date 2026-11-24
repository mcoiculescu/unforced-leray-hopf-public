import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_8
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_8.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_8.L3.Of

/-!
# `slice_id_all` (task `PartIII-b:C/ward/12/3/1/2/7/1/8/3`) — SOLVED by organizer ot1

Source `the November 2 reference manuscript`
lines 2562-2564.  `SliceIdAllOf.slice_id_all_of` (helper file `L3/Of.lean`: countable dense set of
points, reflected kernel `ρ(q - ·)`, continuity of both convolutions) applied to `slice_weak_ae`
(file `L2.lean`).  This file is complete; do not rewrite it.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem slice_id_all : SliceIdAll :=
  SliceIdAllOf.slice_id_all_of fun P _ j f Df hf hDf hW ψ hψ hψc =>
    slice_weak_ae P j f Df hf hDf hW ψ hψ hψc

end UnforcedLeray.Short.PartIIIb.Concrete
