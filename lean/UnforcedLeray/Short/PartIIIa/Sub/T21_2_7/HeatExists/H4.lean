import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H4.SemigroupS0
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H4.SemigroupGrad

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/4`: (H4) the adjoint heat semigroup

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050.  Statement: `HeatExists/Leaves.lean` (`AdjHeatSemigroup`).

Assembly of the two semigroup laws `adjHeatSemigroupS0` (H4.1) and `adjHeatSemigroupGrad` (H4.2)
through `adjHeatSemigroup_of` (`HeatExists/LeavesOf.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjHeatSemigroup (m : ℝ) (hm : 8 < m) : AdjHeatSemigroup m :=
  adjHeatSemigroup_of m (adjHeatSemigroupS0 m hm) (adjHeatSemigroupGrad m hm)

end UnforcedLeray.Short.IIIa
