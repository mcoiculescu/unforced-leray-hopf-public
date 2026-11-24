import UnforcedLeray.Short.PartIIb.Sub.G4_2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize

/-!
# Part II-b, task `PartII-b:G4/2` (`FrozenStreamBounds`): assembly

Source: `the November 2 reference manuscript`, lines 2347-2358.

Assembles `frozenStreamBounds` from the three leaf assemblies `planarStreamSmooth` (task
`PartII-b:G4/2/1`), `planarStreamQuadSplit` (task `PartII-b:G4/2/2`) and `periodizeCoreCut`
(task `PartII-b:G4/2/3`) via the compiled conditional theorem `frozenStreamBounds_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem frozenStreamBounds : UnforcedLeray.Short.IIb.FrozenStreamBounds :=
  frozenStreamBounds_of planarStreamSmooth planarStreamQuadSplit periodizeCoreCut

end UnforcedLeray.Short.IIb
