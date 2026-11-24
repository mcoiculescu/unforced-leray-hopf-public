import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.E1ChangeVar

/-!
# Part III-a, task `PartIII-a:T21/2/2/3/5/1`: `E1ChangeVar` (SP 2860-2864, 3036-3037)

The change of variables `x = √a y` of the cell integral. The proof is the already compiled
direct proof `e1ChangeVar_direct` of `Sub/T21_2_2_1_F1/E1ChangeVar.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- **`E1ChangeVar`** (SP 2860-2864, 3036-3037): `revE1 = physE1 ∘ revAge` on the flow window. -/
theorem e1ChangeVar (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.E1ChangeVar m :=
  e1ChangeVar_direct m

end UnforcedLeray.Short.IIIa.AdjE1
