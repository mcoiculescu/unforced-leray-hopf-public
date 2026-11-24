import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.AgeSurf
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VResidual
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.RepJet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.RepairSource
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.PhaseGradient
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.CoefChg

/-!
# `PartIII-b:C/rep/3`: Body error estimate (`BodyError`)

Source of record: `the November 2 reference manuscript`, lines 5196–5299, 5691–5692.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bodyError (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.BodyError :=
  bodyError_of vResidualOf D hst (repAgeSurf D hst) (repVBg D hst)
    (repJet D hst (phaseGradient D hst)) (coefChg D hst) (repairSource D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
