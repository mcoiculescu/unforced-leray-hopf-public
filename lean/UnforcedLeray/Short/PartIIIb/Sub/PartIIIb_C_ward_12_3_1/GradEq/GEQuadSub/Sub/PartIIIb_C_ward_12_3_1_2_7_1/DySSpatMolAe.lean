import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_8
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_8.L3

/-!
# `dyS_spatMol_ae`

Source `the November 2 reference manuscript`
lines 2562-2564.  For a.e. `τ`, the classical slice derivative of the spatial mollification is the
mollification of the weak derivative: `dyS_spatMol_ae_of slice_id_all`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem dyS_spatMol_ae : DySSpatMolAe := dyS_spatMol_ae_of slice_id_all

end UnforcedLeray.Short.PartIIIb.Concrete
