import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_3.L1

/-!
# `selComplete`: completeness of `Y_2` on one period

Source `the November 2 reference manuscript` lines 1334-1337, 1341-1344, 1470-1480.
The analytic content is `selCompleteL1` (module `L1`); the periodic extension to all of `ℝ × Space`
is `selComplete_of` (module `PartIII-b_IIIb-D2_1_3_1_2_1_4_1_3_3`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem selComplete : SelComplete := selComplete_of selCompleteL1

end UnforcedLeray.Short.PartIIIb.Concrete
