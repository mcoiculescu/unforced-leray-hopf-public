import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.ProjCommuteProps

/-!
# Bridge: `L0TProjSmoothCommute` is `L0TProjCommute`

Source `the November 2 reference manuscript`
lines 1356-1366.  The restated `L0TProjCommute` (`…_8_2_1.lean`) and `L0TProjSmoothCommute`
(`ProjCommuteProps.lean`) have the same body, so a proof of either is a proof of the other.  The
assembly `l0TSolExtension_proof` (task `PartIII-b:C/ward/12/3/1/2/8/2/1`) can therefore use
`l0TSolExtension_of (l0TProjCommute_of_smoothCommute l0TProjSmoothCommute) l0TSolApprox`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem l0TProjCommute_of_smoothCommute (h : L0TProjSmoothCommute) : L0TProjCommute := h

theorem l0TProjSmoothCommute_of_commute (h : L0TProjCommute) : L0TProjSmoothCommute := h

end UnforcedLeray.Short.PartIIIb.Concrete
