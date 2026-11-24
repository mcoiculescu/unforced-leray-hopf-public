import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1.KerYoungMoment
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1.HeatMoment

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/1`: (H1) Young bound of the adjoint heat kernel

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. Statement: `HeatExists/Leaves.lean` (`AdjHeatS0Young`).
Assembly: `adjHeatS0Young_of` (`HeatExists/LeavesOf.lean`) with `adjKerYoungMoment` and
`adjHeatMoment`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjHeatS0Young (m : ℝ) (hm : 8 < m) : AdjHeatS0Young m :=
  adjHeatS0Young_of m (by linarith) adjKerYoungMoment adjHeatMoment

end UnforcedLeray.Short.IIIa
