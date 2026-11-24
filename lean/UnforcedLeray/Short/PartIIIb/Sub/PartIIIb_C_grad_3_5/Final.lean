import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5.L2

/-!
# `PartIII-b:C/grad/3/5` final: `GradMeas` unconditionally

Assembles `gradMeas_of` (Sub/PartIII-b_C_grad_3_5.lean) with the two leaves `hpAC1`
(Sub/PartIII-b_C_grad_3_5/L1.lean) and `psipAC2` (Sub/PartIII-b_C_grad_3_5/L2.lean).
Source 4979-4980, 5063-5079.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradMeas (as : ℝ) (χf : ℝ → ℝ) : GradMeas as χf :=
  gradMeas_of as χf (hpAC1 as χf) (psipAC2 as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
