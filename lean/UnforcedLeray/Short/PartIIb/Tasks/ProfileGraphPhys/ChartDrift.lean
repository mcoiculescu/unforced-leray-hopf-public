import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_3
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.ChartLiftPairing
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.LocalIntegrable

/-!
# `PartII-b:T10/6/3` (`ChartDrift`): assembly of the two proved leaves

Source of record: `the November 2 reference manuscript`
lines 1912-1915. The leaves `chartLiftPairing_proof` (`PartII-b:T10/6/3/1`) and
`hrLocalIntegrable_proof` (`PartII-b:T10/6/3/2`) are fed to `chartDrift_of` of
`Sub/PartII-b_T10_6_3`.
-/

set_option autoImplicit false

theorem chartDrift_proof : UnforcedLeray.Short.IIb.ChartDrift :=
  UnforcedLeray.Short.IIb.chartDrift_of chartLiftPairing_proof hrLocalIntegrable_proof
