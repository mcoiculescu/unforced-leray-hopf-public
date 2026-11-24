import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3_1

/-!
# `TrPd`: first-order physical derivative of the transported field (`PartIII-b:C/rep/8/2/pres/5/3/2`)

Source of record: `shorter-proof-2026-11-02.tex` lines 4784, 5455, 5267-5268.
`physPd f j y = fderiv ℝ f y (coordinateVector j)` and `‖coordinateVector j‖ = 1`, so the
directional derivative is bounded by the full derivative, which `trFd` bounds by `2‖DG(ofLp y)‖`.
-/

set_option autoImplicit false

noncomputable section

open WithLp

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeanScaleSub

theorem trPd : MeanScaleSub.TrPd := by
  unfold MeanScaleSub.TrPd
  intro G j y hG
  have hd : DifferentiableAt ℝ G (ofLp y) := hG (ofLp y)
  have hn := trFd G y hd
  have hc : ‖coordinateVector j‖ = 1 := by
    simp [coordinateVector]
  unfold physPd
  calc ‖fderiv ℝ (fun y' : Space => toLp 2 (G (ofLp y'))) y (coordinateVector j)‖
      ≤ ‖fderiv ℝ (fun y' : Space => toLp 2 (G (ofLp y'))) y‖ * ‖coordinateVector j‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fun y' : Space => toLp 2 (G (ofLp y'))) y‖ := by rw [hc, mul_one]
    _ ≤ 2 * ‖fderiv ℝ G (ofLp y)‖ := hn

end UnforcedLeray.Short.PartIIIb.Concrete
