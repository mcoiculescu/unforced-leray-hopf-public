import UnforcedLeray.Short.PartIIb.Sub.G1
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.RawProfileLate
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.NvFderiv
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.BoundThroughAxis
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.RawContDiff

/-!
# Part II-b, task `PartII-b:G1`: unconditional form of `StrongLateCoeff`

Source of record: `the November 2 reference manuscript`, lines 2412-2431, display
`short-bg:strong-late-coeff` (SP 2417). Assembles `strongLateCoeff_of` (`Sub/G1.lean`) from the four
leaf modules `RawProfileLate`, `NvFderiv`, `BoundThroughAxis`, and `RawContDiff`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem strongLateCoeff_proof : UnforcedLeray.Short.IIb.StrongLateCoeff :=
  strongLateCoeff_of rawProfileLate nvFderivBound boundThroughAxis rawContDiff

end UnforcedLeray.Short.IIb
