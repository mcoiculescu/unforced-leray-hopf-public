import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Deriv.ChangeVar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Deriv.AgeDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Deriv.PhysDeriv

/-!
# Part III-a, task `PartIII-a:T21/2/2/3/5` (`e1MovingDeriv`): assembly

Source of record: `the November 2 reference manuscript` (SP) lines 2860-2864,
2945-2957, 3060-3062, 3137-3139. `E1MovingDeriv m` is assembled from the three leaves
`E1ChangeVar` (`Deriv/ChangeVar.lean`), `RevAgeDeriv` (`Deriv/AgeDeriv.lean`) and `E1PhysDeriv`
(`Deriv/PhysDeriv.lean`) by the chain rule `e1MovingDeriv_of` (`PartIIIa_T21_2_2_3_5.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- **`e1MovingDeriv`** (SP 2860-2864, 2945-2957, 3060-3062, 3137-3139): assembly of the three
leaves by the chain rule through `revAge`. -/
theorem e1MovingDeriv (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjE1.E1MovingDeriv m :=
  e1MovingDeriv_of m (e1ChangeVar m) (revAgeDeriv m) (e1PhysDeriv m hm)

end UnforcedLeray.Short.IIIa.AdjE1
