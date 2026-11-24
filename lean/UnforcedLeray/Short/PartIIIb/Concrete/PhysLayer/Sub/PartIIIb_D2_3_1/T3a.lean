import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1

/-!
# `WardX0Decay` holds unconditionally (`PartIII-b:IIIb-D2/3/1/3/1/1`, task `PartIII-b:IIIb-D2/3/1/3/1`)

Source of record: `the November 2 reference manuscript` 4175-4186 (decay 4177-4179).
Composes the conditional `wardX0Decay_of` (`Sub/PartIII-b_IIIb-D2_3_1_3_1.lean`) with the
unconditional far-field bound `wardX0FarBound` (`L1.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardX0Decay_unconditional (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) :
    WardX0Decay c mZ ρb γ ν ε μ hχo :=
  UnforcedLeray.Short.PartIIIb.Concrete.wardX0Decay_of c mZ ρb γ ν ε μ hχo
    (wardX0FarBound c mZ ρb γ ν ε μ hχo)

end UnforcedLeray.Short.PartIIIb.Concrete

end
