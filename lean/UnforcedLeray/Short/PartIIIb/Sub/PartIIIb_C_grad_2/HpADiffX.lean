import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_1.HpTermMajorant
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable

/-!
# `PartIII-b:C/grad/2/1` (draft): `HpADiffX` assembled from the term majorant and the summability

Source `the November 2 reference manuscript` lines 4973-4980, 4741-4745, 5081-5084.
Assembles `hpADiffX_of` from `hpTermMajorant` and `hpPsiTermSummable`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpADiffX (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : HpADiffX as χf :=
  hpADiffX_of as χf hpTermMajorant hpPsiTermSummable

end UnforcedLeray.Short.PartIIIb.Concrete
