import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Sub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Raw
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.VSup
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9.RhoW1

/-!
# `PartIII-b:C/rep/8/2/pres/4/2/1`: Sup bound `CoefChgSup D`

Source: `the November 2 reference manuscript` lines 2715-2725.
Assembles `coefChgSup_of` from `rawSupBound` (`PartIII-b:C/rep/8/2/pres/4/2/1/1`),
`repairStanding_rhoW1` (`PartIII-b:C/rep/9/2`), and `vSupBound` (`PartIII-b:C/rep/8/2/pres/4/2/1/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem coefChgSup (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : CoefChgSup D :=
  coefChgSup_of D hst (rawSupBound D hst) (repairStanding_rhoW1 D hst) (vSupBound D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
