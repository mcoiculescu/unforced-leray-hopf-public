import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2_1_3
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.ChartSectionEq
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.PsiQMP.Azimuth
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.PsiQMP.GDiff
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.PsiQMP.NullImage
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift.PsiQMP.DomainAC

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **`T10/2/1/3`**: `PsiQMP` from the four leaf facts and `ChartSectionEq`. -/
theorem psiQMP_proof : UnforcedLeray.Short.IIb.PsiQMP :=
  psiQMP_proof_of chartSectionEq_proof psi_azimuth psi_g_diff null_image_dim4 psi_domain_ac

end UnforcedLeray.Short.IIb
