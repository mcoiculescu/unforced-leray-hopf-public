import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.TransverseTail.Leaves
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds.PhysKopYoungLateBounds.KOutChart

/-!
# `PartII-b:T20/2/1` (`KOutChartAe`): a.e. chart identification of the physical interaction output

Source of record: `the November 2 reference manuscript` (SP), lines 2007–2012.
Re-exports `UnforcedLeray.Short.IIb.PhysKopYLKOut.kOutChartAe` as `kOutChartAe_proof`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

/-- **Target of `PartII-b:T20/2/1`**: a.e. chart identification `g = kOutChart p b Qb Eb` on the
strip `s > 0, |q| < c / 2` for `IsKOut p b g`. -/
theorem kOutChartAe_proof : UnforcedLeray.Short.IIb.KOutChartAe :=
  UnforcedLeray.Short.IIb.PhysKopYLKOut.kOutChartAe

end UnforcedLeray.Short.IIb
