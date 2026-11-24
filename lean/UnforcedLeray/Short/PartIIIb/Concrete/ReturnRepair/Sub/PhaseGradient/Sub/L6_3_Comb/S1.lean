import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1a
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_1_HRep

/-!
# `sepX0KerInt` (`PartIII-b:C/rep/2/6/3/1`)

Source of record: `the November 2 reference manuscript` 3603-3626 (`sep:kernel`,
`sep:resolvent`), 4171-4174.  The statement `SepX0KerInt` follows from the joint integrability
of the `Gker` integrand (`gkerIntegrable`, `PartIII-b:C/rep/2/6/3/1/1`) and the h-representation
`sepWHRep` (`PartIII-b:C/rep/2/6/1`) via `sepX0KerInt_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`sepX0KerInt`** (`PartIII-b:C/rep/2/6/3/1`): `X₀ = Re kerInt Kd` off the old disk. -/
theorem sepX0KerInt : SepX0KerInt :=
  sepX0KerInt_of gkerIntegrable sepWHRep

end UnforcedLeray.Short.PartIIIb.Concrete
