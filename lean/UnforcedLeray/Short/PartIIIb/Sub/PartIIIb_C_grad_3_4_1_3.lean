import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_1.HpTermMajorant
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_4.SVBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2_4.BallMajor

/-!
# `PartIII-b:C/grad/3/4/1/3`: `GradLatticeSmooth`

Source `the November 2 reference manuscript`
4963-4980, 5063-5079.  Assembly of the proved leaves: `gradLatticeSmooth_of`
(`Sub/PartIII-b_C_grad_3_4_1_3/Of.lean`) applied to `hpTermMajorant`
(`Sub/PartIII-b_C_grad_2_1/HpTermMajorant.lean`), `pamxSVBound` and `pamxBallMajor`
(`Sub/PartIII-b_C_grad_2_4/SVBound.lean`, `Sub/PartIII-b_C_grad_2_4/BallMajor.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradLatticeSmooth : GradLatticeSmooth :=
  gradLatticeSmooth_of hpTermMajorant pamxSVBound pamxBallMajor

end UnforcedLeray.Short.PartIIIb.Concrete
