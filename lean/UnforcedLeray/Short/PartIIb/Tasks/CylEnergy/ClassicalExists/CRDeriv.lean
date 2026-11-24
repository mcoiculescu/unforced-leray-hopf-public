import UnforcedLeray.Short.PartIIb.Sub.T22_1_10_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatGrad
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCommute
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRDeriv.Diff
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRDeriv.Cont

/-!


Proves `CRDeriv` (`Sub/T22_1_10.lean`) from `crDeriv_of` (`Sub/T22_1_10_1.lean`), the
`HeatGradFormula` and `HeatCommute` leaves, and the leaves `dDiff` (`CRDeriv/Diff.lean`) and
`dCont` (`CRDeriv/Cont.lean`).
Source `the November 2 reference manuscript`, lines 2074-2093 and 2103-2105.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

/-- **`PartII-b:T22/1/10/1`** `CRDeriv`, assembled from the leaves. -/
theorem crDeriv : UnforcedLeray.Short.IIb.CylPDE.CRDeriv :=
  crDeriv_of heatGradFormula heatCommute dDiff dCont

end UnforcedLeray.Short.IIb.CylPDE
