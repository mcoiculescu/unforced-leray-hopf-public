import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.L5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13.L6

/-!
# `truncEq`: the truncated equation

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
`truncEq` is obtained from the assembly `truncEq_of` (`Sub/PartIII-b_IIIb-D2_1_3_1_2_1_13`) applied to
the six ingredients `truncCurlIntertwine` (L1), `truncCutCurlTest` (L2), `truncCurlMove` (L3),
`truncCommutator` (L4), `truncSpgStep` (L5) and `truncSplit` (L6).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem truncEq : TruncEq :=
  truncEq_of truncCurlIntertwine truncCutCurlTest truncCurlMove truncCommutator truncSpgStep
    truncSplit

end UnforcedLeray.Short.PartIIIb.Concrete
