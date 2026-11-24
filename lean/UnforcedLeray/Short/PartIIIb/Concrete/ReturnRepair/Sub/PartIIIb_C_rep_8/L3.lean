import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Org

/-!
# `PartIII-b:C/rep/8/3`: `GaussianReplace` (source 5484-5498, 5272-5289)

Source of record: `the November 2 reference manuscript`, lines 5484-5498, 5272-5289.
Assembles `gaussianReplace` from `gaussianReplace_of`, `grMeas_proof`, and `grBound_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`PartIII-b:C/rep/8/3`**: Gaussian replacement (`GaussianReplace`, source 5484-5498, 5272-5289). -/
theorem gaussianReplace (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.GaussianReplace :=
  gaussianReplace_of D (grMeas_proof D) (grBound_proof D hst) hst.chiF

end UnforcedLeray.Short.PartIIIb.Concrete
