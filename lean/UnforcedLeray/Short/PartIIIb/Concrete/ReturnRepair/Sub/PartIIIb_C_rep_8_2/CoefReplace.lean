import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.ChgPt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.HolderConv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.L2Conv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.PresFlat
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.CoefChg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResSplitMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_3

/-!
# `PartIII-b:C/rep/8/2/4`: `D.CoefReplace`

Source: `the November 2 reference manuscript` lines 5272-5289, 5494-5506.
Assembles `coefReplace` from `SeqData.coefReplace_of` and the 9 leaf theorems.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem coefReplace (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.CoefReplace :=
  D.coefReplace_of hst wardEXYChgPt ringHolderConv ringL2Conv (meanResMeas D hst)
    (meanResSplitMeas D hst) (presFlat D hst) (coefChg D hst) (meanGrad D hst) (entJet D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
