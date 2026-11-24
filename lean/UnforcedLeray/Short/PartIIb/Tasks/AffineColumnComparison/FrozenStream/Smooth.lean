import UnforcedLeray.Short.PartIIb.Sub.G4_2_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseOrderTwo
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth

/-!
# Part II-b, task `PartII-b:G4/2/1` (`PlanarStreamSmooth`): assembly

Source: `the November 2 reference manuscript`, lines 2347-2352.

Assembles `planarStreamSmooth` from the two leaf theorems `greenInverseOrderTwo` (leaf
`PartII-b:G4/2/1/1`) and `greenInverseSqSmooth` (leaf `PartII-b:G4/2/1/2`) via the compiled
conditional theorem `planarStreamSmooth_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem planarStreamSmooth : UnforcedLeray.Short.IIb.PlanarStreamSmooth :=
  planarStreamSmooth_of greenInverseOrderTwo greenInverseSqSmooth

end UnforcedLeray.Short.IIb
