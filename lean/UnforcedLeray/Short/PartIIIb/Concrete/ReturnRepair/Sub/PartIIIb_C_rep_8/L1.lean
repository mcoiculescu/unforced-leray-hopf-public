import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomComparison
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.HessianBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.YoungSupport
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.MeanMeasurable
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.BackgroundSplit

/-!
# `PartIII-b:C/rep/8/1`: `D.MeanComparisonAzi`

Source: `the November 2 reference manuscript` lines 5415-5448 with 5272-5289, 5376.
Assembles `meanComparison` from `D.meanComparison_of` and the five leaf theorems.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem meanComparison (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.MeanComparisonAzi :=
  D.meanComparison_of hst (geomComparison D hst) (hessianBound D hst) (youngSupport D hst)
    (meanMeasurable D hst) (backgroundSplit D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
