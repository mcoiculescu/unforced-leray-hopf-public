import UnforcedLeray.Short.PartIIb.Sub.T22_1_10
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRDeriv
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRSize
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRCont
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRPer

/-!


Proves `ConvRegular` (`Sub/T22_1/Stages.lean`) from the four leaves `crDeriv`, `crSize`,
`crCont`, `crPer` via `convRegular_of` (`Sub/T22_1_10.lean`).
Source `the November 2 reference manuscript`, lines 2074-2093 and 2103-2105.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

/-- **`PartII-b:T22/1/10`** `ConvRegular`, assembled from the four leaves. -/
theorem convRegular : UnforcedLeray.Short.IIb.CylPDE.ConvRegular :=
  convRegular_of crDeriv crSize crCont crPer

end UnforcedLeray.Short.IIb.CylPDE
