import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_4

/-!
# `PartIII-b:C/grad/3/4/1`: `GradEnvelope` assembled from the leaves

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.  Proved: `gradEnvelope`, by
`gradEnvelope_of (gradEntryChain gradLatticeHp gradLatticePsi gradLatticeSmooth)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradEnvelope : GradEnvelope :=
  gradEnvelope_of (gradEntryChain gradLatticeHp gradLatticePsi gradLatticeSmooth)

end UnforcedLeray.Short.PartIIIb.Concrete
