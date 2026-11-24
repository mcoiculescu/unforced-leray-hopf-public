import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2_5.KopX
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2_5.KopS

/-!
# `PartIII-b:C/grad/3/4/1/1/2/5`: `𝒦` envelope of `h^p_A` (assembly of the two halves)

Source `the November 2 reference manuscript`
5063-5079.  Assembles `gradHpKEnv` from `gradKopXEnv` (KopX.lean) and `gradKopSEnv` (KopS.lean)
through `gradHpKEnv_of` (compiled in `PartIII-b_C_grad_3_4_1_1_2_5.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradHpKEnv : GradHpKEnv := gradHpKEnv_of gradKopXEnv gradKopSEnv

end UnforcedLeray.Short.PartIIIb.Concrete
