import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5.Final
import UnforcedLeray.Short.PartIIIb.Concrete.AffineGradPin.GradLeaf1
import UnforcedLeray.Short.PartIIIb.Concrete.AffineGradPin.GradLeaf2
import UnforcedLeray.Short.PartIIIb.Concrete.AffineGradPin.GradLeaf3
import UnforcedLeray.Short.PartIIIb.Concrete.AffineGradPin.GradLeaf4
import UnforcedLeray.Short.PartIIIb.Concrete.AffineGradPin.GradLeaf6

/-!
# `PartIII-b:C/grad/3`: `GradCoefBound`

Assembly of `gradCoefBound_of` (`Sub/PartIII-b_C_grad_3.lean`) from the leaves
`gradSupport` (GradLeaf1), `ayIterBound` (GradLeaf2), `ayContDiffAt2` (GradLeaf3),
`gradCellBound` (GradLeaf4), `gradMeas` (`Sub/PartIII-b_C_grad_3_5/Final.lean`), and
`gradL2Conv` (GradLeaf6).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradCoefBound (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) :
    GradCoefBound as χf :=
  gradCoefBound_of as χf hχ (gradSupport χf) (ayIterBound as χf) (ayContDiffAt2 as χf)
    gradCellBound (gradMeas as χf) gradL2Conv

end UnforcedLeray.Short.PartIIIb.Concrete
