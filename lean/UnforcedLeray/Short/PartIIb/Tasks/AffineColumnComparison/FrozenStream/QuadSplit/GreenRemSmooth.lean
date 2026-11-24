import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.SmoothA
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.SmoothB
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.PolyZpow

/-!
# Part II-b, task `PartII-b:G4/2/2/3`: `greenRemSmooth`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: `greenRemSmooth_of` (Sub/G4_2_2_3.lean) applied to the task files `smoothA`, `smoothB`,
`polyZpow`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem greenRemSmooth : UnforcedLeray.Short.IIb.GreenRemSmooth :=
  greenRemSmooth_of smoothA smoothB polyZpow

end UnforcedLeray.Short.IIb
