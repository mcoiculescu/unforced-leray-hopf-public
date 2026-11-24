import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2_1
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.ChartSectionEq
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.ChartCompAesm
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.PsiQMP

/-!
# Part II-b, task `PartII-b:T10/2/1` (`ProfileMeasOfLift`): assembly

Source of record: `the November 2 reference manuscript` (SP) lines 1897-1906.
The leaves `chartSectionEq_proof`, `chartCompAesm_proof`, `psiQMP_proof` feed `profileMeasOfLift_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem profileMeasOfLift_proof : UnforcedLeray.Short.IIb.ProfileMeasOfLift :=
  profileMeasOfLift_of chartSectionEq_proof chartCompAesm_proof psiQMP_proof

end UnforcedLeray.Short.IIb

end
