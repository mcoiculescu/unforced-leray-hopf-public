import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.ChartForm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.RbForm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.RbY
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.Pointwise

/-!
# `CoefChgLp` (task `PartIII-b:C/rep/8/2/pres/4/2/lp`)

Source `the November 2 reference manuscript` 5287-5289, 2669, 5134-5139.
The four pieces are proved in the lemma files of `Sub/PartIII-b_C_rep_8_2_pres_4_2_lp/`
(`chartFormPhaseLr`, `rbChartForm`, `rbYBound`, `coefChgPointwise`) and assembled by
`coefChgLp_of` (the organizer file).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem coefChgLp (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : CoefChgLp D :=
  coefChgLp_of D chartFormPhaseLr (rbChartForm D hst) (rbYBound D hst) (coefChgPointwise D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
