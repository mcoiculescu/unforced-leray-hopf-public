import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs

/-!
# `OD_Zero` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/1`)

`outerTransp h 0 = id`: exponentials at `0` are `1`, the heat time is `0`, the dilation is
`dilN 1`, and the phase translation is `transC 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odZero : OD_Zero := by
  intro P _ h Ψ
  unfold outerTransp
  simp only [neg_zero, zero_div, Real.exp_zero, inv_one, sub_self, mul_zero, Complex.ofReal_one,
    one_smul]
  rw [UnforcedLeray.B0223.heatC_of_nonpos le_rfl, UnforcedLeray.B0223.dilN_one,
    UnforcedLeray.B0223.transC_zero]

end UnforcedLeray.Short.PartIIIb.NearInst
