import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_1_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.PolyZpow
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.SmoothA
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.SmoothB
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RqPolyAt.MulPoly
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RqPolyAt.Lin
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RqPolyAt.IntA
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RqPolyAt.IntB

/-!
# Part II-b, task `PartII-b:G4/2/2/1/5`: `RqPolyAt`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: assemble the four leaf estimates (`polyMulPoly`, `polyLin`, `polyIntA`, `polyIntB`)
together with `polyZpow`, `smoothA`, `smoothB` through `rqPolyAt_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem rqPolyAt : UnforcedLeray.Short.IIb.RqPolyAt :=
  rqPolyAt_of polyZpow polyMulPoly polyLin smoothA smoothB polyIntA polyIntB

end UnforcedLeray.Short.IIb
