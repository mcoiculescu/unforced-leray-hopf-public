import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.LiftNice
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.LiftDriftProfile
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.NvCLin
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.LiftPairing

/-!
# `PartII-b:T10/6/3/1` (`ChartLiftPairing`): assembly from the proved leaves

Source of record: `the November 2 reference manuscript`
lines 1912-1915 and 1900-1906. The leaves `liftNice_proof`, `liftDriftProfile_proof`,
`nvCLin_proof`, `liftPairing_proof` are applied to the assembly `chartLiftPairing_of` of `Lift.lean`.
-/

theorem chartLiftPairing_proof : UnforcedLeray.Short.IIb.ChartLiftPairing :=
  UnforcedLeray.Short.IIb.ChartLift.chartLiftPairing_of
    UnforcedLeray.Short.IIb.ChartLift.liftNice_proof
    UnforcedLeray.Short.IIb.ChartLift.liftDriftProfile_proof
    UnforcedLeray.Short.IIb.nvCLin_proof
    liftPairing_proof
