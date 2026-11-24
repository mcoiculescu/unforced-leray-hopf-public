import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B4a
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B4b

/-!
# `outPrimSmoothInf_proved` (`PartIII-b:IIIb-D2/3/2/11/2/5`, source 4177-4179)

Source of record: `the November 2 reference manuscript`.
`outPrimSmoothInf_of` (`PartIII-b_IIIb-D2_3_2_11_2_5.lean`) applied to the three proved facts

* `wardX0SmoothInf_proved` (B1.lean, joint `C^∞` of `X₀` on the young region),
* `wardX0IntegrandDecay_proved` (B4b.lean, all-order decay of the integrand),
* `paramIntSmooth_proved` (B4a.lean, smooth dependence of `-∫_{Ioi r} G`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **`outPrimSmoothInf_proved`** (source 4177-4179): the outward primitive of `X₀` is jointly
`C^∞` on `r > R√(5ν/6)`. -/
theorem outPrimSmoothInf_proved : OutPrimSmoothInf :=
  outPrimSmoothInf_of wardX0SmoothInf_proved wardX0IntegrandDecay_proved paramIntSmooth_proved

end UnforcedLeray.Short.PartIIIb.Concrete
