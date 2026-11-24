import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.Bridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.ProjCommute
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.SolApprox

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1`: the solution extension `L0TSolExtension` (assembly)

Source `the November 2 reference manuscript` lines 1356-1366, 1446-1455.
One-line assembly: `l0TSolExtension_of` (in `PartIII-b_C_ward_12_3_1_2_8_2_1.lean`) applied to
`l0TProjCommute_of_smoothCommute l0TProjSmoothCommute` and `l0TSolApprox`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem l0TSolExtension_proof : L0TSolExtension :=
  l0TSolExtension_of (l0TProjCommute_of_smoothCommute l0TProjSmoothCommute) l0TSolApprox

end UnforcedLeray.Short.PartIIIb.Concrete

end
