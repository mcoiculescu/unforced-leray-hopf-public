import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S2a

/-!
# `sepX0TauDeriv` (`PartIII-b:C/rep/2/6/3/2`)

Source `the November 2 reference manuscript` lines 3603-3626, 4171-4200.
The statement `SepX0TauDeriv` is `sepX0TauDeriv_of` applied to `sepX0KerInt` (S1,
`PartIII-b:C/rep/2/6/3/1`) and `kerIntKdDeriv` (S2a, `PartIII-b:C/rep/2/6/3/2/1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`sepX0TauDeriv`** (`PartIII-b:C/rep/2/6/3/2`): the `τ`-derivative of `sepX0`. -/
theorem sepX0TauDeriv : SepX0TauDeriv :=
  sepX0TauDeriv_of sepX0KerInt kerIntKdDeriv

end UnforcedLeray.Short.PartIIIb.Concrete
