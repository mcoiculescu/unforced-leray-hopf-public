import UnforcedLeray.Short.PartIIb.Sub.R1
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingResidualProved
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SliceFieldElem
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.LerayOnForce
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingResidualAxisymmetric
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RawIsRingLift
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingLiftSmoothExt
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingResidualCartesianNS
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SmoothResidualWeakForm

/-!
# Part II-b, task `PartII-b:R1`: unconditional form of `RawResidualFamily`

Source of record: `the November 2 reference manuscript`, lines 2042-2046
(`sct:residual-bound`, `V_0 = U_raw`). Assembles `rawResidualFamily_of` (`Sub/R1.lean`) from the
eight leaf modules under `RawResidualFamily/` and `PartIIa.ringAxisSmooth` (`PartII-a:R06`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem rawResidualFamily_proof : UnforcedLeray.Short.IIb.RawResidualFamily :=
  rawResidualFamily_of ringResidualBound_proved
    (rawResidualWeakIdentity_of rawIsRingLift_proof
      (ringLiftSmoothExt_of UnforcedLeray.Short.PartIIa.ringAxisSmooth)
      ringResidualCartesianNS_proof smoothResidualWeakForm_proof)
    (lerayOfPeriodicLp_of sliceFieldElem_proof lerayOnForce_proof)
    ringResidualAxisymmetric_proof

end UnforcedLeray.Short.IIb
