import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.Decomp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.L3

/-!
# `PartIII-b:C/grad/3/4/1/1`: the lattice envelope `GradLatticeHp`

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.  Proved: `gradLatticeHp` from the three leaves
`gradLatticeSummable` (L1), `gradHpTermEnv` (L2), `gradHpTsum` (L3) through `gradLatticeHp_of`
(Decomp).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradLatticeHp : GradLatticeHp :=
  gradLatticeHp_of gradLatticeSummable gradHpTermEnv gradHpTsum

end UnforcedLeray.Short.PartIIIb.Concrete
