import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGradOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.KernelPt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.WeightInt

/-!
# The mean-field gradient estimate `D.MeanGrad` (`PartIII-b:C/rep/8/2/pres/5`)

Source of record: `the November 2 reference manuscript`
lines 5282-5284 (`‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22}N₁`), 5203-5217, 5267-5268, 5380-5387, 5400-5413.

The pointwise kernel bound `meanJetKernelPt` (`MeanGrad/KernelPt.lean`, task pres/5/4) and the
`(s, η)` integral `youngJetWeightInt` (`MeanGrad/WeightInt.lean`, task pres/5/5) are fed into the
assembly `meanGrad_of` (`MeanGradOrg.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`meanGrad`**: the mean-field gradient estimate `D.MeanGrad` along the sequence. -/
theorem meanGrad (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.MeanGrad :=
  meanGrad_of D hst (meanJetKernelPt D.K.χo D.K.χy) youngJetWeightInt

end UnforcedLeray.Short.PartIIIb.Concrete
