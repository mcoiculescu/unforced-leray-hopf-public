import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_4.SDerivTsum
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_4.SVBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_4.BallMajor

/-!
# `PartIII-b:C/grad/2/4` (draft): the mixed derivative `∂_x ∂_s ψ^p_A` exists at `s > 0`

Source `the November 2 reference manuscript` lines 4973-4980.
Assembles `psipAMixedX_of` from the three leaves `pamxSDerivTsum`, `pamxSVBound`, `pamxBallMajor`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psipAMixedX (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : PsipAMixedX as χf :=
  psipAMixedX_of as χf hχ (pamxSDerivTsum as χf) pamxSVBound pamxBallMajor

end UnforcedLeray.Short.PartIIIb.Concrete
