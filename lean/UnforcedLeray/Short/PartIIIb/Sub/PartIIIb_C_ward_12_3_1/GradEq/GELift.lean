import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8.G1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8.G2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8.G3

/-!
# `PartIII-b:C/ward/12/3/1/2/8`: `GELift`

Assembly of `gELift_of` (`Sub/PartIII-b_C_ward_12_3_1_2_8.lean`) from the three leaves
`gEGradSol_proof` (G1), `gEBodyUniqueSol_proof` (G2), and `gELerayPairSol_proof` (G3).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gELift : GELift :=
  gELift_of gEGradSol_proof gEBodyUniqueSol_proof gELerayPairSol_proof

end UnforcedLeray.Short.PartIIIb.Concrete
