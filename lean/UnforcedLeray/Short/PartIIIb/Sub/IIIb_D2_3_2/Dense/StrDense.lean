import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_1.LpDense
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_1.FiniteCompacts
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_1.NullSeam

/-!
# Density of the stresses with smooth chart representatives (`PartIII-b:IIIb-D2/3/2/11/1`, source 4284-4286, 2666-2700)

`strSmoothDense_proved : StrSmoothDense` (for all parameters), from the generic density
`lpSmoothDense_proved` and the measure facts `GainMeasuresOK`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gainMeasuresOK_proved : GainMeasuresOK := by
  intro c mZ ρb γ ν hc hν
  obtain ⟨h1, h2⟩ := gainMeasures_finiteOnCompacts c mZ ρb γ ν hc hν
  obtain ⟨h3, h4⟩ := gainMeasures_null_off_chartDom c mZ ρb γ ν hc
  exact ⟨h1, h2, h3, h4⟩

theorem strSmoothDense_proved (c mZ ρb γ ν : ℝ) : StrSmoothDense c mZ ρb γ ν :=
  strSmoothDense_of lpSmoothDense_proved gainMeasuresOK_proved c mZ ρb γ ν

end UnforcedLeray.Short.PartIIIb.Concrete
