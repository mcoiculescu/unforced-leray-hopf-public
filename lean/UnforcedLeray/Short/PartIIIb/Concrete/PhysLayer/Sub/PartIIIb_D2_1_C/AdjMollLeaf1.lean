import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollDivKernel

/-!
# Leaf 1 of `FWUAdjMoll`: the mollification is a solenoidal phase test

Source: `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
The target `MollIsSolTestL` is discharged by `mollIsSolTestL_of` from the two leaves
`mollLocInt` (local integrability of `Φ`) and `mollDivKernel` (the divergence identity
against the periodised reflected kernel).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem mollIsSolTestL : MollIsSolTestL :=
  mollIsSolTestL_of mollLocInt mollDivKernel

end UnforcedLeray.Short.PartIIIb.Concrete
