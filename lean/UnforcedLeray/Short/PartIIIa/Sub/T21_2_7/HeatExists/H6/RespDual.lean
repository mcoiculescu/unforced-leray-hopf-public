import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H5.S0Dual
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H6.GradDual

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/6/1`: (H6.1) the dual identity of the response

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. Statement: `HeatExists/Leaves.lean` (`AdjHeatRespDual`).
Assembly: `adjHeatRespDual_of` (`HeatExists/LeavesOf.lean`) from `adjHeatS0Young` (H1),
`adjHeatGradYoung` (H2), `adjHeatS0Dual` (H5.1) and `adjHeatGradDual` (H6.1a).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjHeatRespDual (m : ℝ) (hm : 8 < m) : AdjHeatRespDual m :=
  adjHeatRespDual_of m (adjHeatS0Young m hm) (adjHeatGradYoung m hm)
    (adjHeatS0Dual m hm) (adjHeatGradDual m hm)

end UnforcedLeray.Short.IIIa
