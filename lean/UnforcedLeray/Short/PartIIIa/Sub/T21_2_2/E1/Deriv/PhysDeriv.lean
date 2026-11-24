import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Deriv.PhysDiff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Deriv.PhysRate

/-!
# Part III-a, task `PartIII-a:T21/2/2/3/5/3` (`e1PhysDeriv`): assembly

Source of record: `the November 2 reference manuscript` (SP) lines 2860-2864,
2945-2957, 3060-3062, 3137-3139. `E1PhysDeriv m` is the derivative identity of `physE1` at the
reverse age, split by `e1PhysDeriv_of` into the two leaves `E1PhysDiff` (`Deriv/PhysDiff.lean`,
`e1PhysDiff`) and `E1PhysRate` (`Deriv/PhysRate.lean`, `e1PhysRate`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- **`e1PhysDeriv`** (SP 2860-2864, 2945-2957, 3060-3062, 3137-3139): assembly of the two leaves. -/
theorem e1PhysDeriv (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjE1.E1PhysDeriv m :=
  e1PhysDeriv_of m (e1PhysDiff m hm) (e1PhysRate m hm)

end UnforcedLeray.Short.IIIa.AdjE1
