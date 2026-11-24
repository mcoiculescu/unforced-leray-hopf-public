import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_red
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.L1_far
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1.L2
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `WardX0FarBound` holds unconditionally (`PartIII-b:IIIb-D2/3/1/3/1/1`)

Source of record: `the November 2 reference manuscript` 4156-4186, 3604-3621.
Composes the conditional `wardX0FarBound_of` (`L1_red.lean`) with
* `oldSourceReg_all` (`Sub/IIIb-D2_3_1_1/L1.lean`), the unconditional `OldSourceReg`,
* `sepFarDecay` (`L1_far.lean`), the unconditional far-field decay,
* `sepWSmoothOn_of IIIa.sepKernelBounds` (`Sub/IIIb-D2_3_1_1/L2.lean`), smoothness of `sepW`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wardX0FarBound (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) :
    WardX0FarBound c mZ ρb γ ν ε μ hχo :=
  wardX0FarBound_of c mZ ρb γ ν ε μ hχo
    (oldSourceReg_all c mZ ρb γ ν ε hχo)
    sepFarDecay
    (sepWSmoothOn_of UnforcedLeray.Short.IIIa.sepKernelBounds)

end UnforcedLeray.Short.PartIIIb.Concrete

end
