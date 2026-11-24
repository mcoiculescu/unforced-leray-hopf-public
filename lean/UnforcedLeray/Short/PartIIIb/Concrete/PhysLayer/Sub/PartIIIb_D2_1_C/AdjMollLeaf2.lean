import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLeaf1

/-!
# Leaf 2 of `FWUAdjMoll`: the unconditional graph condition `MollGraphInYr`

Source: `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
`mollGraphInYr_of` (Sub file `PartIII-b_IIIb-D2_1_3_1_2_2_2`) reduces `MollGraphInYr` to
`MollIsSolTestL`, which is discharged unconditionally by `mollIsSolTestL` (leaf 1).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem mollGraphInYr : MollGraphInYr :=
  mollGraphInYr_of mollIsSolTestL

end UnforcedLeray.Short.PartIIIb.Concrete
