import UnforcedLeray.Short.PartIIIa.Sub.ParamsWideBridges
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream

/-!
# Part III-a, task `PartIII-a:T23/3`: the inlet coefficient bounds

Source of record: `the November 2 reference manuscript`, lines 2711-2727 and 2347-2362.

`InletCoeffBounds` is discharged by `inletCoeffBounds_of_frozen` from the frozen stream bounds
`IIb.frozenStreamBounds` (task `PartII-b:G4/2`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem inletCoeffBounds : InletCoeffBounds :=
  inletCoeffBounds_of_frozen UnforcedLeray.Short.IIb.frozenStreamBounds

end UnforcedLeray.Short.IIIa
