import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.RbFacts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.RepPhasePointwise
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.VelSliceMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.HolderPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.VelPhysL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.PeriodSmall

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `PartIII-b:C/rep/1` (source 5169-5176, `repair:source`): the repair source bound, assembled
from the six leaf statements of the `Sub/PartIII-b_C_rep_1` decomposition. -/
theorem repairSource (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.RepairSource :=
  repairSource_of D hst rbFacts repPhasePointwise velSliceMeas holderPhase velPhysL2 periodSmall

end UnforcedLeray.Short.PartIIIb.Concrete
