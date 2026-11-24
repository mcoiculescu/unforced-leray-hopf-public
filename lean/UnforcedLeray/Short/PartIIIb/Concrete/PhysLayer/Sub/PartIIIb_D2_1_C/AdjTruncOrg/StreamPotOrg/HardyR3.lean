import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.HardySmooth
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.Approx

/-!
# `hardyR3`: the Hardy inequality in `ℝ³` for `L⁶` fields with `L²` weak gradient

Source `the November 2 reference manuscript` lines 1351-1362.

Assembly of the two analytic inputs: `hardySmooth` (Hardy inequality for `C_c^∞` fields) and
`hardyApprox_holds` (`C_c^∞` approximation of `u ∈ L⁶` with weak gradient in `L²`), through
`hardyR3_of`, which contains the Fatou limit passage.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The Hardy inequality in `ℝ³` (source 1351-1362): `HardyR3` holds. -/
theorem hardyR3 : HardyR3 := hardyR3_of hardySmooth hardyApprox_holds

end UnforcedLeray.Short.PartIIIb.Concrete
