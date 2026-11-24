import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLeaf1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLeaf2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLeaf3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLeaf4

/-!
# `FWUAdjMoll`: assembly of the four mollification leaves

Source: `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
`fwuAdjMoll_of` (Sub file `PartIII-b_IIIb-D2_1_3_1_2_2`) reduces `FWUAdjMoll` to the four
leaves `MollIsSolTestL`, `MollGraphInYr`, `MollApproxIdentity`, `MollCommutatorLimit`,
each discharged by the compiled leaf files `AdjMollLeaf1`..`AdjMollLeaf4`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fwuAdjMoll : FWUAdjMoll :=
  fwuAdjMoll_of mollIsSolTestL mollGraphInYr mollApproxIdentity mollCommutatorLimit

end UnforcedLeray.Short.PartIIIb.Concrete
