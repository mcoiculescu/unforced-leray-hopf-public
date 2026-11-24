import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4.L2

/-!
# `PartIII-b:C/grad/3/4`: `GradCellBound`

One-line assembly of `gradCellBound_of` (`Sub/PartIII-b_C_grad_3_4.lean`) from the leaves
`gradEnvelope` (L1) and `gradLatticeL2` (L2).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradCellBound : GradCellBound :=
  gradCellBound_of gradEnvelope gradLatticeL2

end UnforcedLeray.Short.PartIIIb.Concrete
