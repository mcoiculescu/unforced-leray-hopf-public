import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1.WtBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1.Pointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1.L2Diff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1.ProductRule

/-!
# `PartIII-a:T21/2/2/2/2/1`, assembly of `ReyPhysDeriv`

Source: `the November 2 reference manuscript` (SP) lines 3060-3073.
The four leaves `wtPhysBound`, `physE0Pointwise`, `physE0L2Diff`, `weightedProductRule`
feed `reyPhysDeriv_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

theorem reyPhysDeriv (m : ℝ) (hX : UnforcedLeray.Short.IIIa.AdjXDiff m) :
    UnforcedLeray.Short.IIIa.E0.ReyPhysDeriv m :=
  reyPhysDeriv_of m (wtPhysBound m) (physE0Pointwise m) (physE0L2Diff m) weightedProductRule hX

end UnforcedLeray.Short.IIIa.E0
