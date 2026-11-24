import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Fubini

/-!
# `adjDomGrad`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Assembly of `AdjDomGrad` from the slice-wise regularity `adjDomGradSlice` and the Fubini step
`adjDomGradFubini`, via `adjDomGrad_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem adjDomGrad : AdjDomGrad :=
  adjDomGrad_of adjDomGradSlice adjDomGradFubini

end UnforcedLeray.Short.PartIIIb.Concrete
