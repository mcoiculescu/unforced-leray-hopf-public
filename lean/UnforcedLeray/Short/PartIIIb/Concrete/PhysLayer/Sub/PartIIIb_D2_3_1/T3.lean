import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.PartIIIb_IIIb_D2_3_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3a
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3b
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3c

/-!
# `OutPrimStream` holds unconditionally (`PartIII-b:IIIb-D2/3/1/3`)

Source of record: `the November 2 reference manuscript` 4175-4186.
Composes the conditional `outPrimStream_of_aux` (`Sub/PartIII-b_IIIb-D2_3_1_3.lean`) with
* `Final.wardX0Smooth_of` (`T1.lean`), `Final.wardX0Structure_of` (`T2.lean`),
* `wardX0Decay_unconditional` (`T3a.lean`), and the generic derivative statements
  `outPrimDerivR` (`T3b.lean`) and `outPrimDerivZ` (`T3c.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem outPrimStream_of (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) :
    OutPrimStream c mZ ρb γ ν ε μ hχo :=
  outPrimStream_of_aux c mZ ρb γ ν ε μ hχo
    (UnforcedLeray.Short.PartIIIb.Concrete.Final.wardX0Smooth_of c mZ ρb γ ν ε μ hχo)
    (UnforcedLeray.Short.PartIIIb.Concrete.Final.wardX0Structure_of c mZ ρb γ ν ε μ hχo)
    (wardX0Decay_unconditional c mZ ρb γ ν ε μ hχo)
    outPrimDerivR outPrimDerivZ

end UnforcedLeray.Short.PartIIIb.Concrete

end
