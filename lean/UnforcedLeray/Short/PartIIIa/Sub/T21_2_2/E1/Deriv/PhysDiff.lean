import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_1.WBound
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_1.L2Diff
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_1.Split

/-!
# Part III-a, task `PartIII-a:T21/2/2/3/5/3/1`: `E1PhysDiff` (SP 2860-2864, 3060-3073)

`physE1` is differentiable at the age `r = revAge ν s ζ` with the explicit fixed-cell derivative
`physDerivForm`: the product rule with `(a⁻²)'` (`e1PhysDiff_of`) and, for each `k`, the weighted
product rule `weightedProductRule` applied to `∂_kφ` (`e1PhysTerm_of`), from the leaves
`physWBound`, `physE1L2Diff` (from `adjXDiff`, `w = [k]`) and `wprSplit`
(`Sub/PartIII-a_T21_2_2_3_5_3_1.lean` and its folder).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- **`E1PhysDiff`** (SP 2860-2864, 3060-3073). -/
theorem e1PhysDiff (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjE1.E1PhysDiff m :=
  e1PhysDiff_of_leaves m (physWBound m) (physE1L2Diff m) wprSplit

end UnforcedLeray.Short.IIIa.AdjE1
