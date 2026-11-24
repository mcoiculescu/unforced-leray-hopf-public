import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingChart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanJet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.TrainMoment
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.CoefReplace
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanSupport
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst

/-!
# `PartIII-b:C/rep/8/2`: `D.RingExpansion`

Source: `the November 2 reference manuscript` lines 5449-5506.
Assembles `ringExpansion` from `SeqData.ringExpansion_of_full`, `SeqData.ringExpansionFull_of`,
and the leaf theorems.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ringExpansion (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h6 : D.ActualJet) (h7 : D.JetClock) : D.RingExpansion :=
  D.ringExpansion_of_full
    (D.ringExpansionFull_of hst h6 h7 (coefReplace D hst)
      (ringSubst_of D hst h6 h7 (ringChartRules D hst) (meanJet D hst) (trainMoment D hst))
      (trainMoment D hst) (meanSupport D hst))

end UnforcedLeray.Short.PartIIIb.Concrete
