import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1_2.Exists
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1_2.Young

/-!
# `PartIII-b:C/rep/4/2/org/1/1/2`: `SepWeakExistenceThin`

One-line assembly of `sepWeakExistenceThin_of` (`Sub/PartIII-b_C_rep_4_2_org_1_1_2.lean`)
from the leaves `sepInvExists` (`Exists.lean`) and `sepInvYoung` (`Young.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepWeakExistenceThin (dm dp : ℝ) : SepWeakExistenceThin dm dp :=
  sepWeakExistenceThin_of (sepInvExists dm dp) (sepInvYoung dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
