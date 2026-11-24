import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_ent
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_1_3

/-!
# Organizer task `PartIII-b:C/rep/8/2/pres/4/org2/1`: `entWPt`

Source `the November 2 reference manuscript` 2347-2356 (period rate `2π/c`,
`c = ν⁻²`), 2389-2390, 2516-2520. `EntWPt` (restated with the period rate `m₁ν²`) is discharged
by `entWPt_of` from the inlet chart jets (`inletChartJet`) and the coefficient-change calculus
(`coefChgSumLe`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem entWPt (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : EntWPt D :=
  entWPt_of inletChartJet coefChgSumLe D hst

end UnforcedLeray.Short.PartIIIb.Concrete
