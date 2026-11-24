import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIBPLeaves.FmrIBPInt
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIBPLeaves.FmrIBPDiff
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIBPLeaves.FmrIBPTrans

/-!
# `PartIII-a:T21/c2/2/5`: `FmrIBP` assembled from its three leaves (SP 2950-2954)

`fmrIBP` is `fmrIBP_of` applied to `fmrIBPInt`, `fmrIBPDiff` and `fmrIBPTrans`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem fmrIBP : FmrIBP :=
  fmrIBP_of fmrIBPInt fmrIBPDiff fmrIBPTrans

end UnforcedLeray.Short.IIIa
