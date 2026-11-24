import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Val
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Der
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.KopEnv

/-!
# `PartIII-b:C/grad/3/4/1/1/2`: termwise envelope of `h^p_A` (assembly of the three leaves)

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.  Proved: `gradHpTermEnv` by `gradHpTermEnv_of` applied to
`gradHpValEnv` (Val.lean), `gradHpDerEnv` (Der.lean), `gradHpKEnv` (KopEnv.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradHpTermEnv : GradHpTermEnv :=
  gradHpTermEnv_of gradHpValEnv gradHpDerEnv gradHpKEnv

end UnforcedLeray.Short.PartIIIb.Concrete
