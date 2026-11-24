import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf5

/-!
# Part II-b, task `PartII-b:G4/2/1/2` (`GreenInverseSqSmooth`): assembly

Source: `the November 2 reference manuscript`, lines 2347-2352.

Assembles `greenInverseSqSmooth` from the five leaf theorems
`greenSqContinuous`, `greenSqVolterra`, `sqVolterraExists`, `sqVolterraSmooth`,
`sqVolterraUnique` via `greenInverseSqSmooth_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem greenInverseSqSmooth : UnforcedLeray.Short.IIb.GreenInverseSqSmooth :=
  greenInverseSqSmooth_of greenSqContinuous greenSqVolterra sqVolterraExists
    sqVolterraSmooth sqVolterraUnique

end UnforcedLeray.Short.IIb
