import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower.Int
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower.Chi
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower.IBP
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower.GradYoung
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Lower.Transport

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`PartIII-a:T21/2/7/2/2/1/2/3/6`**: `AdjCutE0Lower` from the five leaves (i)-(v)
(`cutLowerInt`, `cutLowerChi`, `cutLowerIBP`, `cutLowerGradYoung`, `cutLowerTransport`). -/
theorem adjCutE0Lower (m : ℝ) : AdjCutE0Lower m :=
  adjCutE0Lower_of m (cutLowerInt m) (cutLowerChi m) (cutLowerIBP m)
    (cutLowerGradYoung m) (cutLowerTransport m)

end UnforcedLeray.Short.IIIa
