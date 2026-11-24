import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.CoefChg
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingResidualProved

/-!
# `PartIII-b:C/rep/8/2/pres/3/2`: `PresFlatBound D`

Source: `the November 2 reference manuscript` lines 5245-5281, 1205-1225, 5254-5257, 5277-5279.
Assembles `presFlatBound` from `presFlatBound_of_leaves` and the seven leaf/input theorems.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem presFlatBound (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    PresFlatBound D :=
  presFlatBound_of_leaves D hst (presHelmholtz D hst) (presChgPhys D hst) (presForcePhys D hst)
    (rawResid_of D hst UnforcedLeray.Short.IIb.ringResidualBound_proved)
    (D.entSrc hst) (coefChg D hst) (exactGradBound D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
