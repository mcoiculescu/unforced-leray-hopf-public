import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GreenRemTail
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GaussTail
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GaussMulPoly
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GaussLin
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.PolyZpow

/-!
# Part II-b, task `PartII-b:G4/2/2/2`: `GreenRemDecay`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: apply `greenRemDecay_of` to the five compiled lemma files
`greenRemTail`, `gaussTail`, `gaussMulPoly`, `gaussLin`, `polyZpow`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem greenRemDecay : UnforcedLeray.Short.IIb.GreenRemDecay :=
  greenRemDecay_of greenRemTail gaussTail gaussMulPoly gaussLin polyZpow

end UnforcedLeray.Short.IIb

end
