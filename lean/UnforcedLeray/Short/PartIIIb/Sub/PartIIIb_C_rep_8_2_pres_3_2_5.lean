import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_5.Of
import UnforcedLeray.Short.PartIIa.Tasks.R07BoundedDerivs

/-!
# `exactGradBound` (task `PartIII-b:C/rep/8/2/pres/3/2/5`)

Source `the November 2 reference manuscript`
lines 1217-1219, 1322-1325. Combines `SeqData.exactGradBound_of` with
`UnforcedLeray.Short.PartIIa.ringBoundedDerivs`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Global spatial gradient bound for the exact velocity field along the return sequence
(source lines 1217-1219, 1322-1325). -/
theorem exactGradBound (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.ExactGradBound :=
  SeqData.exactGradBound_of UnforcedLeray.Short.PartIIa.ringBoundedDerivs D hst

end UnforcedLeray.Short.PartIIIb.Concrete
