import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.L3

/-!
# `PartIII-b:C/rep/2/4/5` : `vertYoungPhase`

Composition of the three analytic pieces `vertKernLb` (L1), `vert1DYoung` (L2), `vertDil` (L3)
into `vertYoungPhase_of` (Of.lean), giving `VertYoungPhase` (`Sub/PartIII-b_C_rep_2_4.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `VertYoungPhase` (source 3624-3647, 5219-5221 in one dimension). -/
theorem vertYoungPhase : VertYoungPhase :=
  vertYoungPhase_of vertKernLb vert1DYoung vertDil

end UnforcedLeray.Short.PartIIIb.Concrete
