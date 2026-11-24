import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2.Assembly_C_rep_8_2_pres_4_2

/-!
# `PartIII-b:C/rep/8/2/pres/4`: `D.CoefChg`

Assembles `coefChg` from `coefChg_of`, `coefChgMeas`, and `coefChgQuant`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem coefChg (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.CoefChg :=
  coefChg_of D hst (coefChgMeas D hst) (coefChgQuant D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
