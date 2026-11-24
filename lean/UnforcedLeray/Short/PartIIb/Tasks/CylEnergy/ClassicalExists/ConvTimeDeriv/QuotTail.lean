import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11_4_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.Int
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.TailLim
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.TailWindow
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.TailOutside

/-!


Source: `the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
The tail statement is assembled from `convTD_Quot_tail_of` (Sub file) with the integrability
input `convTD_Int` and the three sibling lemmas `convTD_Tail_Lim`, `convTD_Tail_Window`,
`convTD_Tail_Outside`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

theorem convTD_Quot_tail : UnforcedLeray.Short.IIb.CylPDE.ConvTD_Quot_Tail :=
  convTD_Quot_tail_of convTD_Int convTD_Tail_Lim convTD_Tail_Window convTD_Tail_Outside

end UnforcedLeray.Short.IIb.CylPDE
