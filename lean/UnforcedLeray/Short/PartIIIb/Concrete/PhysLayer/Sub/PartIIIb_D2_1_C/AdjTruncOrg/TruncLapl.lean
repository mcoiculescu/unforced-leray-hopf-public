import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11_5

/-!
# `truncLapl`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Assembly of `TruncLapl` from `laplMem` (`lapA ∈ Y_2`) and `laplPair` (`νΔΦₙ = lapA` weakly)
via `truncLapl_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **truncLapl** (source 1334-1362, 1470-1480): `νΔΦₙ ∈ Y_2` weakly. -/
theorem truncLapl : TruncLapl := truncLapl_of laplMem laplPair

end UnforcedLeray.Short.PartIIIb.Concrete
