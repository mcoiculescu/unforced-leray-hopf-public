import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L9
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L10
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L11
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2_1.L12

/-!
# `PartIII-b:C/grad/3/4/1/2/1`: termwise envelope of `ψ^p_A` (assembly)

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.  The five leaves `gBoundProp`, `gPsiProp`, `gDqProp`,
`gDetaProp`, `gKopProp` are proved in `L2`, `L9`, `L10`, `L11`, `L12`; they feed
`gradPsiTermEnv_of` (Sub file).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradPsiTermEnv : GradPsiTermEnv :=
  gradPsiTermEnv_of gBoundProp gPsiProp gDqProp gDetaProp gKopProp

end UnforcedLeray.Short.PartIIIb.Concrete
