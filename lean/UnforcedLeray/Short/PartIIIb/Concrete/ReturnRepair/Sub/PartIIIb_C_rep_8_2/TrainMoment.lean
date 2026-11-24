import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.L2

/-!
# `PartIII-b:C/rep/8/2/3`: Assembly of `SeqData.TrainMoment`

Source: `the November 2 reference manuscript` lines 5464-5465, 5477-5482,
5484-5495, 2045-2051.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Weighted train moment bounds `TrainMoment` assembled from `tmMeas`, `tmPt`, and `tmL2`
(source lines 5464-5465, 5477-5482, 5484-5495). -/
theorem trainMoment (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.TrainMoment :=
  trainMoment_of D hst tmMeas (tmPt D) (tmL2 D)

end UnforcedLeray.Short.PartIIIb.Concrete
