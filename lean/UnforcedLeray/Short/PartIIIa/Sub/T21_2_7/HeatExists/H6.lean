import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H6.RespDual
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H6.RespTime

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/6`: (H6) tested Duhamel identity of the response

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. Statement: `HeatExists/Leaves.lean` (`AdjHeatDuhamelWeak`).

Assembly of the two sub-leaves through `adjHeatDuhamelWeak_of` (`HeatExists/LeavesOf.lean`):
the dual identity of the response (H6.1) and its time identity (H6.2).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjHeatDuhamelWeak (m : ℝ) (hm : 8 < m) : AdjHeatDuhamelWeak m :=
  adjHeatDuhamelWeak_of m (adjHeatRespDual m hm) (adjHeatRespTime m hm)

end UnforcedLeray.Short.IIIa
