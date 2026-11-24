import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLipZeroCirc
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLipBSSub
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLipBSBound

/-!
# `PartIII-a:T21/2/3/1/4` (`ladVelLip`)

Assembles the three leaves through `ladVelLip_of`:
* `ladFlowZeroCirc m (1 < m)` (`VelLipZeroCirc.lean`);
* `ladBSSub m` (`VelLipBSSub.lean`);
* `ladBSBound m (8 < m)` (`VelLipBSBound.lean`).

Source: `the November 2 reference manuscript` 3230-3240, 2819-2830, 270-288.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

theorem ladVelLip (m : ℝ) (hm : 8 < m) : LadVelLip m :=
  ladVelLip_of m hm (ladFlowZeroCirc m (by linarith)) (ladBSSub m) (ladBSBound m hm)

end UnforcedLeray.Short.IIIa
