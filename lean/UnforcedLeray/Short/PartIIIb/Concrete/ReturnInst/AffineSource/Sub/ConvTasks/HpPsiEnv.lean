import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.HpPsiEnvOf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3

/-!
# `PartIII-b:C/asrc/ra/9/2/2/12`: `HpPsiEnv`

One-line application of `hpPsiEnv_of` (`ConvTasks/HpPsiEnvOf.lean`) to the three grad leaves
`gradLatticeHp` (`PartIII-b_C_grad_3_4_1_1`), `gradLatticePsi` (`PartIII-b_C_grad_3_4_1_2`),
and `gradLatticeSmooth` (`PartIII-b_C_grad_3_4_1_3`).
Source `the November 2 reference manuscript` lines 4963-4980, 5036-5039, 5063-5079.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpPsiEnv (as : ℝ) : HpPsiEnv as :=
  hpPsiEnv_of gradLatticeHp gradLatticePsi gradLatticeSmooth as

end UnforcedLeray.Short.PartIIIb.Concrete
