import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2.L1

/-!
# No hidden null space on the solenoidal sector (source 1393-1400, 1409-1412, 1358-1359)

Task `PartIII-b:C/ward/12/3/1/2/8/2`.  Source of record
`the November 2 reference manuscript`.

Assembly only: `gEBodyUniqueSol_of` (in `PartIII-b_C_ward_12_3_1_2_8_2.lean`) applied to the
extension `l0TSolExtension_proof` (in `PartIII-b_C_ward_12_3_1_2_8_2/L1.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gEBodyUniqueSol_proof : GEBodyUniqueSol :=
  gEBodyUniqueSol_of l0TSolExtension_proof

end UnforcedLeray.Short.PartIIIb.Concrete

end
