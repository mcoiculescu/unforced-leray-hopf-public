import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_4.Subseq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_4.AeLimits
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_4.SliceL2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_4.WeakPass

/-!
# `selLimit`: limit identification on slices

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
The four analytic inputs are `selSubseq` (module `Subseq`), `selAeSliceLimits` (module `AeLimits`),
`selAeSliceL2` (module `SliceL2`) and `selWeakPass` (module `WeakPass`); the assembly is `selLimit_of`
(module `PartIII-b_IIIb-D2_1_3_1_2_1_4_1_3_4`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem selLimit : SelLimit :=
  selLimit_of selSubseq selAeSliceLimits selAeSliceL2 selWeakPass

end UnforcedLeray.Short.PartIIIb.Concrete
