import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_1_1_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspApprox.DensContinuous
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspApprox.DensSmooth

/-!
# `PartIII-a:T21/2/3/1/9/1/1/1`: `ladDensApprox` (`LadDensApprox`)

Source `the November 2 reference manuscript` lines 3230-3240.

Assembly: `ladDensApprox_of` (proved in the parent decomposition file) applied to the two
leaves `ladDensContinuous` (continuous periodic band approximants) and `ladDensSmooth`
(smoothing of those).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `LadDensApprox m` from the two leaves. The hypothesis `8 < m` is not needed for the
assembly itself. -/
theorem ladDensApprox (m : ℝ) (hm : 8 < m) : LadDensApprox m :=
  ladDensApprox_of m ladDensContinuous ladDensSmooth

end UnforcedLeray.Short.IIIa
