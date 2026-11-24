import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1.KerYoungMoment
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H2.GradMoment

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/2`: (H2) Young bound of the gradient of the adjoint heat kernel

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. Statement: `HeatExists/Leaves.lean` (`AdjHeatGradYoung`).
Assembly: `adjHeatGradYoung_of` (`HeatExists/LeavesOf.lean`) with `adjKerYoungMoment` and
`adjHeatGradMoment`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjHeatGradYoung (m : ℝ) (hm : 8 < m) : AdjHeatGradYoung m :=
  adjHeatGradYoung_of m (by linarith) adjKerYoungMoment adjHeatGradMoment

end UnforcedLeray.Short.IIIa
