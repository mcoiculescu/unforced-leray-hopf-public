import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.AdvInt
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundQ

/-!
# Part I, task `PartI:T08/7/3` (`JTQuad`): assembly from `JTAdvInt` and `JTBoundQ`

Source: `the November 2 reference manuscript` lines 352-358.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target** `jtQuad_proof` (task `PartI:T08/7/3`): `JTQuad`, assembled by `jtQuad_of`
from `jtAdvInt_proof` and `jtBoundQ_proof`. -/
theorem jtQuad_proof : UnforcedLeray.Short.PartI.JTQuad :=
  jtQuad_of jtAdvInt_proof jtBoundQ_proof

end UnforcedLeray.Short.PartI
