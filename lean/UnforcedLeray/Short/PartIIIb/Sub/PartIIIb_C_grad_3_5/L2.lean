import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1.T1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2.T2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2.T3

/-!
# `PartIII-b:C/grad/3/5/2` leaf L2: `PsipAC2` from the three inputs

Assembles `psipAC2_of` (aggregator `Sub/PartIII-b_C_grad_3_5_2.lean`) with
`tsumContDiffOnBounds` (`Sub/PartIII-b_C_grad_3_5_1/T1.lean`), `psipATermC2`
(`Sub/PartIII-b_C_grad_3_5_2/T2.lean`) and `psipALocUnif` (`Sub/PartIII-b_C_grad_3_5_2/T3.lean`).
Source 4974-4980, 5063-5079, 4741-4745.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psipAC2 (as : ℝ) (χf : ℝ → ℝ) : PsipAC2 as χf :=
  psipAC2_of as χf tsumContDiffOnBounds (psipATermC2 as) (psipALocUnif as)

end UnforcedLeray.Short.PartIIIb.Concrete
