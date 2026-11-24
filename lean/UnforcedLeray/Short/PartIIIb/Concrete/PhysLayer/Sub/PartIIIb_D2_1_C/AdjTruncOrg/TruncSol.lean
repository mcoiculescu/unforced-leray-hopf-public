import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10_5

/-!
# `truncSol`: the truncated field is weakly solenoidal

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Assembly of `TruncSol` from `truncSol_of` (`Sub/PartIII-b_IIIb-D2_1_3_1_2_1_10`) with the
three ingredients `weakSolOfCurl`, `weakCurlMul` and `truncGCurl`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem truncSol : TruncSol :=
  truncSol_of weakSolOfCurl weakCurlMul truncGCurl

end UnforcedLeray.Short.PartIIIb.Concrete
