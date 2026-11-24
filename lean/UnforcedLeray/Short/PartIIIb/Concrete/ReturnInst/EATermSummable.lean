import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable.Hess
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable.Mgrad

/-!
# `C/inst/3`: summability of the lattice terms of `e_A` (source 4971-4972, 4978)

Assembles `EATermSummable` from the two analytic leaves `hessVjBound` (Hess.lean) and
`mgradPjBound` (Mgrad.lean) through `eATermSummable_of` (Sub/PartIII-b_C_inst_3.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem eATermSummable : EATermSummable :=
  eATermSummable_of hessVjBound mgradPjBound

end UnforcedLeray.Short.PartIIIb.Concrete

end
