import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S5

/-!
# `sepX0Comb` (`PartIII-b:C/rep/2/6/3`)

Source of record: `the November 2 reference manuscript` lines 4199-4200, 5223.
The statement `SepX0Comb` is `sepX0Comb_of` applied to the five analytic inputs
`sepX0KerInt` (S1), `sepX0TauDeriv` (S2), `sepX0YGrad` (S3), `sepX0Lap` (S4) and `kdOpSplit` (S5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`sepX0Comb`** (`PartIII-b:C/rep/2/6/3`): the combined `D_{μ+1}` identity for `X₀`. -/
theorem sepX0Comb : SepX0Comb :=
  sepX0Comb_of sepX0KerInt sepX0TauDeriv sepX0YGrad sepX0Lap kdOpSplit

end UnforcedLeray.Short.PartIIIb.Concrete
