import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_11
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_11_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_11_2

/-!
# `nearBody` (`PartIII-b:C/rep/11`, source 5540-5547, 5551-5552, 5621-5622)

Assembles `D.NearBody` from `ropFreeBodyBound` (`PartIII-b:C/rep/11/1`) and `multOpNormBound`
(`PartIII-b:C/rep/11/2`) via `SeqData.nearBody_of` (`Sub/PartIII-b_C_rep_11.lean`).
Source of record: `the November 2 reference manuscript` lines 5540-5547.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`nearBody`** (`PartIII-b:C/rep/11`, 5540-5547). -/
theorem nearBody (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.NearBody :=
  D.nearBody_of hst.omega_ne (ropFreeBodyBound D hst) (multOpNormBound D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
