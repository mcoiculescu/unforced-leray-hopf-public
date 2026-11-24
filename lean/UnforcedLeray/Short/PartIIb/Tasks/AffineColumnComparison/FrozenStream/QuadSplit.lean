import UnforcedLeray.Short.PartIIb.Sub.G4_2_2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.EigenGaussDecay
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GreenRemDecay
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GreenRemSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RadialAngularDecay

/-!
# Part II-b, task `PartII-b:G4/2/2` (`PlanarStreamQuadSplit`): assembly

Source: `the November 2 reference manuscript`, lines 2349-2352.

Assembles `planarStreamQuadSplit` from the four leaf theorems `eigenGaussDecay`, `greenRemDecay`,
`greenRemSmooth`, `radialAngularDecay` (leaves `PartII-b:G4/2/2/1` to `/4`) via the compiled
conditional theorem `planarStreamQuadSplit_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem planarStreamQuadSplit : UnforcedLeray.Short.IIb.PlanarStreamQuadSplit :=
  planarStreamQuadSplit_of eigenGaussDecay greenRemDecay greenRemSmooth radialAngularDecay

end UnforcedLeray.Short.IIb
