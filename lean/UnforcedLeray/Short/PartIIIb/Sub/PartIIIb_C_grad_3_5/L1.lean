import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1.T1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1.T2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1.T3

/-!
# `PartIII-b:C/grad/3/5/1` leaf L1: `HpAC1` from the three inputs

Assembles `hpAC1_of` (aggregator `Sub/PartIII-b_C_grad_3_5_1.lean`) with
`tsumContDiffOnBounds` (`Sub/PartIII-b_C_grad_3_5_1/T1.lean`), `hpATermC1`
(`Sub/PartIII-b_C_grad_3_5_1/T2.lean`) and `hpALocUnif` (`Sub/PartIII-b_C_grad_3_5_1/T3.lean`).
Source 4973-4980, 4991, 5063-5079, 4741-4745.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpAC1 (as : ℝ) (χf : ℝ → ℝ) : HpAC1 as χf :=
  hpAC1_of as χf tsumContDiffOnBounds (hpATermC1 as) (hpALocUnif as)

end UnforcedLeray.Short.PartIIIb.Concrete
