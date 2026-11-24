import UnforcedLeray.Short.PartIIb.Sub.P1
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Norm

/-!
# Part II-b, task `PartII-b:P1` (`bodyLift_iso`): the body lift `J`

Source of record: `the November 2 reference manuscript`, lines 1902-1906.
Assembly of `bodyLift_of` (`Sub/P1.lean`) with the two leaves `bodyLiftLinear_proof`
(`Tasks/BodyLift/Linear.lean`, `PartII-b:P1/1`) and `bodyLiftNorm_proof`
(`Tasks/BodyLift/Norm.lean`, `PartII-b:P1/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:P1`** (`bodyLift_iso`; SP 1902-1906, 2490-2504). -/
theorem bodyLift_iso : UnforcedLeray.Short.IIb.BodyLift :=
  bodyLift_of bodyLiftLinear_proof bodyLiftNorm_proof

end UnforcedLeray.Short.IIb
