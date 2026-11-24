import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileOfNoSwirl
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift

/-!
# `PartII-b:T10/6` (`DriftRecovery`): assembly of the three proved leaves

Source of record: `the November 2 reference manuscript`, lines 1912-1915.
The leaves `driftNoSwirl_proof` (`T10/6/1`), `profileOfNoSwirl_proof` (`T10/6/2`) and
`chartDrift_proof` (`T10/6/3`) are fed to `driftRecovery_of` of `Sub/PartII-b_T10_6`.
-/

set_option autoImplicit false

theorem driftRecovery_proof : UnforcedLeray.Short.IIb.DriftRecovery :=
  UnforcedLeray.Short.IIb.driftRecovery_of driftNoSwirl_proof
    UnforcedLeray.Short.IIb.profileOfNoSwirl_proof chartDrift_proof
