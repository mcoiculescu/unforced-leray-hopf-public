import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.Int
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.Bdry
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvTimeDeriv.Quot

/-!


Composes the three leaf results `convTD_Int`, `convTD_Quot`, `convTD_Bdry` through
`convTimeDeriv_of` (Sub/PartIIb_T22_1_11.lean). Source of record:
`the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

theorem convTimeDeriv : UnforcedLeray.Short.IIb.CylPDE.ConvTimeDeriv :=
  convTimeDeriv_of convTD_Int convTD_Quot convTD_Bdry

end UnforcedLeray.Short.IIb.CylPDE

end
