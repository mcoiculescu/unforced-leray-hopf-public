import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L6

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

/-- `PartII-a:N01/6/2` change of variables over one period with the age weight (source 2666-2668,
2684-2687): `ChartPhaseLIntegral` for `F p = ofReal (p.1 ^ 2) * G p`, then `AgeWeightShift`. -/
theorem chartPhaseFrob : UnforcedLeray.Short.PartIIa.N01.ChartPhaseFrob := by
  intro R c hR hc G hG
  have hF : Measurable (fun p : UnforcedLeray.Short.PartIIIb.Concrete.Chart =>
      ENNReal.ofReal (p.1 ^ 2) * G p) :=
    ((measurable_fst.pow_const 2).ennreal_ofReal).mul hG
  have h1 := UnforcedLeray.Short.PartIIIb.Concrete.chartPhaseLIntegral R c hR hc _ hF
  have h2 := UnforcedLeray.Short.PartIIIb.Concrete.ageWeightShift c hc G hG
  refine h1.trans ?_
  simp only [h2]

end UnforcedLeray.Short.PartIIa.N01
