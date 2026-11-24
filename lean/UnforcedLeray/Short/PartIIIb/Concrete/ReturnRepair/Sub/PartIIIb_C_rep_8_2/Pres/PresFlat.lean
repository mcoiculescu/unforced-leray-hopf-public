import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2

/-!
# `PartIII-b:C/rep/8/2/pres/3`: `D.PresFlat`

Assembles `presFlat` from `presFlat_of`, `presFlatMeas`, and `presFlatBound`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem presFlat (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.PresFlat :=
  presFlat_of D hst (presFlatMeas D hst) (presFlatBound D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
