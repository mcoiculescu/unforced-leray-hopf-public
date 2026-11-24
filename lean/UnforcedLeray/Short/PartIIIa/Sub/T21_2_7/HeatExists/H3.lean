import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H3.TestLimit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H3.TestDense

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/3`: (H3) strong continuity at age zero

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. Statement: `HeatExists/Leaves.lean` (`AdjHeatS0StrongZero`).

Assembly of the three sub-leaves through `adjHeatS0StrongZero_of` (`HeatExists/LeavesOf.lean`):
the Young bound (H1), convergence on complexified cylinder tests (H3.1), and density of those
tests (H3.2).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjHeatS0StrongZero (m : ℝ) (hm : 8 < m) : AdjHeatS0StrongZero m :=
  adjHeatS0StrongZero_of m (adjHeatS0Young m hm) (adjHeatS0TestLimit m hm)
    (adjCylTestDense m hm)

end UnforcedLeray.Short.IIIa
