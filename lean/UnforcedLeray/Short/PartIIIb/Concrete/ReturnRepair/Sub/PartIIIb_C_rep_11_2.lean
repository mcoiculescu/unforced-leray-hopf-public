import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_11_2_dec
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_11_2_2

/-!
# `PartIII-b:C/rep/11/2`: `multOpNormBound`

Source `the November 2 reference manuscript` 2706-2713, 2775-2777, 3876-3878,
5779-5782. Combines `SeqData.multOpNormBound_of` (`PartIII-b_C_rep_11_2_dec`) with `nearMUGainBound`
(`PartIII-b_C_rep_11_2_2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem multOpNormBound (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.MultOpNormBound :=
  SeqData.multOpNormBound_of D (nearMUGainBound D hst)

end UnforcedLeray.Short.PartIIIb.Concrete

end
