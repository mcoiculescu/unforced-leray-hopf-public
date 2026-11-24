import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_swirl_org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8.L1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8.L2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8.L3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.ActualJet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.JetClock

/-!
# `PartIII-b:C/rep/8`: `D.ThinCompleteAzi`

Source: `the November 2 reference manuscript` lines 5374-5506, 5376.
Assembles `thinComplete` from `thinCompleteAzi_of`, `meanComparison`, `ringExpansion`,
`gaussianReplace`, `actualJet`, and `jetClock`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem thinComplete (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.ThinCompleteAzi :=
  thinCompleteAzi_of D hst (meanComparison D hst)
    (ringExpansion D hst (actualJet D hst) (jetClock D hst)) (gaussianReplace D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
