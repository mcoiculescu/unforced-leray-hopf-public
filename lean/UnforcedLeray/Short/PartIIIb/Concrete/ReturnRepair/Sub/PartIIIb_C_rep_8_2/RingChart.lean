import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1.Val
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1.D1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.D2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1.LiftGrad

/-!
# `RingChartRules` (`PartIII-b:C/rep/8/2/1`, top statement)

Assembly of the four ring-chart expansions: `ringChartRawVal` (Val), `ringChartRawD1` (D1),
`ringChartRawD2` (`Sub/PartIII-b_C_rep_8_2_1_3/D2.lean`, the D2 leaf), and `ringChartLiftGrad`
(LiftGrad) through `ringChartRules_of` (`Sub/PartIII-b_C_rep_8_2_1.lean`).

Source `the November 2 reference manuscript` lines 5460-5465 (exact ring-chart
rules).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ringChartRules (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.RingChartRules :=
  ringChartRules_of ringChartRawVal ringChartRawD1 ringChartRawD2 ringChartLiftGrad D hst

end UnforcedLeray.Short.PartIIIb.Concrete

end
