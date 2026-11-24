import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs

/-!
# `OD_Norm` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/2`)

`‖outerTransp h t Ψ‖ ≤ e^{-t/4} ‖Ψ‖`: the dilation and the phase translation are isometries,
the heat factor is a contraction (`B0223.norm_heatC_apply_le`), and the scalar is `e^{-t/4}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odNorm : OD_Norm := by
  intro P _ h t Ψ
  unfold outerTransp
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    LinearIsometry.norm_map]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  refine (UnforcedLeray.B0223.norm_heatC_apply_le _ _).trans ?_
  rw [UnforcedLeray.B0223.norm_dilN_apply]

end UnforcedLeray.Short.PartIIIb.NearInst
