import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11_4
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.Int
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.QuotGInt
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.QuotInner
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.QuotTail

/-!


Composes the four sibling results `convTD_Int`, `convTD_Quot_gint`, `convTD_Quot_inner`,
`convTD_Quot_tail` through `convTD_Quot_of` (Sub/PartIIb_T22_1_11_4.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

theorem convTD_Quot : UnforcedLeray.Short.IIb.CylPDE.ConvTD_Quot :=
  convTD_Quot_of convTD_Int convTD_Quot_gint convTD_Quot_inner convTD_Quot_tail

end UnforcedLeray.Short.IIb.CylPDE

end
