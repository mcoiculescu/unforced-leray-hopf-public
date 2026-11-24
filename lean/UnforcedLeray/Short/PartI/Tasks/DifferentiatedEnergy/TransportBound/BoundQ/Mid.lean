import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_3_1_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundQ.Mid.Holder3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundQ.Mid.GNWord
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundQ.Mid.Core

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target** `jtQMid_proof` (task `PartI:T08/7/3/1/3`): `JTQMid` from `MidCore`, which is
obtained from `MidHolder3` and `MidGNWord`. -/
theorem jtQMid_proof : UnforcedLeray.Short.PartI.JTQMid :=
  jtQMid_proof_of (midCore_of_parts midHolder3_proof midGNWord_proof)

end UnforcedLeray.Short.PartI
