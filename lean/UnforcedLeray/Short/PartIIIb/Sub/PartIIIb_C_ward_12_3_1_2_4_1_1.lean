import UnforcedLeray.Short.PartIIb.Sub.R1
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RawIsRingLift
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingResidualCartesianNS
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SmoothResidualWeakForm

namespace UnforcedLeray.Short.PartIIIb

/-- Conditional form: the raw residual weak identity from the smooth lift hypothesis
`RingLiftSmoothExt`, with the other three hypotheses discharged by existing proofs. -/
theorem rawResidualWeakIdentity_of_lift (h₂ : UnforcedLeray.Short.IIb.RingLiftSmoothExt) :
    UnforcedLeray.Short.IIb.RawResidualWeakIdentity :=
  UnforcedLeray.Short.IIb.rawResidualWeakIdentity_of
    UnforcedLeray.Short.IIb.rawIsRingLift_proof h₂
    UnforcedLeray.Short.IIb.ringResidualCartesianNS_proof
    UnforcedLeray.Short.IIb.smoothResidualWeakForm_proof

end UnforcedLeray.Short.PartIIIb
