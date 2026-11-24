import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_3
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIBPLeaves.FmrTransGenInt.FmrTransGenInt
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrIBPLeaves.FmrTransGenId.FmrTransGenId

/-!
# `PartIII-a:T21/c2/2/5/3`: `FmrIBPTrans` from its two leaves (SP 2950-2954)

`fmrIBPTrans` is `fmrIBPTrans_of` applied to the leaves `fmrTransGenInt` and `fmrTransGenId`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem fmrIBPTrans : FmrIBPTrans :=
  fmrIBPTrans_of fmrTransGenInt fmrTransGenId

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.fmrIBPTrans
