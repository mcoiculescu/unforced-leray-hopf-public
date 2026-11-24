import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.Of
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H6

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8`: `AdjHeatExists m`

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
(the free part of the Volterra iteration on `X_{-m,c}`) and 3044-3050 (weights on the cell).
Assembly of the six leaves H1-H6 through `adjHeatExists_of` (`HeatExists/Of.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **`AdjHeatExists m`** (SP 2819-2836): assembled from the leaves H1-H6 for `8 < m`. -/
theorem adjHeatExists (m : ℝ) (hm : 8 < m) : AdjHeatExists m :=
  adjHeatExists_of m (adjHeatS0Young m hm) (adjHeatGradYoung m hm)
    (adjHeatS0StrongZero m hm) (adjHeatSemigroup m hm) (adjHeatS0Weak m hm)
    (adjHeatDuhamelWeak m hm)

end UnforcedLeray.Short.IIIa
