import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.Decomp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.P1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.P2

/-!
# `PartIII-b:C/grad/3/4/1/2`: `GradLatticePsi`

One-line assembly of `gradLatticePsi_of` (`Sub/PartIII-b_C_grad_3_4_1_1/Decomp.lean`) from
`gradLatticeSummable` (L1), `gradPsiTermEnv` (P1), and `gradPsiTsum` (P2).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradLatticePsi : GradLatticePsi :=
  gradLatticePsi_of gradLatticeSummable gradPsiTermEnv gradPsiTsum

end UnforcedLeray.Short.PartIIIb.Concrete
