import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds.PhysKopYoungLateBounds.BoundFromChart
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds.PhysKopYoungLateBounds.KOutChart

/-!
# Part II-b, task `PartII-b:G2/2` (`PhysKopYoungLateBounds`)

Source of record: `the November 2 reference manuscript`
(SP), lines 2007–2012 (chart substitution for `K_ε = s B_ε T_ε`), 2412–2431 (`RawProfileLate`),
2434–2437 (late physical tail), and 2443–2445 (young physical tail).

Assembles `physKopYoungLateBounds_proof : UnforcedLeray.Short.IIb.PhysKopYoungLateBounds` from:
* `PhysKopYLKOut.kOutChartAe : KOutChartAe` (identification of `IsKOut p b g` with `kOutChart`
  a.e. on the window strip `s > 0, |q| < c/2`);
* `PhysKopYLHelp.physKopYoungLateBounds_of_chartAe` (young and late `hpIndNorm` bounds from
  `KOutChartAe`, `rawProf_young_chartJet`, `rawProfileLate`, and the `GraphBound` hypothesis).
-/

set_option autoImplicit false

theorem physKopYoungLateBounds_proof : UnforcedLeray.Short.IIb.PhysKopYoungLateBounds :=
  UnforcedLeray.Short.IIb.PhysKopYLHelp.physKopYoungLateBounds_of_chartAe
    UnforcedLeray.Short.IIb.PhysKopYLKOut.kOutChartAe
