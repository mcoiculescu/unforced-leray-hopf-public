import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_1_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.PresFlat
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9.RhoW1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.BackgroundSplit.ActGrad

/-!
# `BackgroundSplit`: the background coefficient split (`PartIII-b:C/rep/8/1/5`)

All definitions, measurability lemmas (`actJetMeas`, `actJetChartTransfer`), reductions
(`coefChg_of_rhoW1`, `respJetGrad_of_act`), and assembly theorems (`backgroundSplit_of`,
`backgroundSplit_of_leaves`, `backgroundSplit_of_actGrad`) are provided by
`UnforcedLeray.Short.«PartIII-b».Sub.«PartIII-b_C_rep_8_1_5»`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem backgroundSplit (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.BackgroundSplit :=
  backgroundSplit_of_actGrad D hst (presFlat D hst) (repairStanding_rhoW1 D hst) (actGrad D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
