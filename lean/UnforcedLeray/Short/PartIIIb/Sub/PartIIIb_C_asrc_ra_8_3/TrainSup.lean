import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3.B1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3.B2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3.B3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3.B4
import UnforcedLeray.Short.PartI.Tasks.ComparisonBootstrap

/-!
# `RTrainSup` (`PartIII-b:C/asrc/ra/8/3/1`; source 5029-5032)

`rTrainSup` follows from `PartI.train_comparison` (`PartI:T09`) by `rTrainSup_of`, using the
four bridge lemmas `vsumEqVc_proof`, `trainDiffSmooth_proof`, `diffMagFromSup_proof`,
`comparisonExpConv_proof` (files B1-B4).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rTrainSup : UnforcedLeray.Short.PartIIIb.Concrete.RTrainSup :=
  rTrainSup_of UnforcedLeray.Short.PartI.train_comparison vsumEqVc_proof trainDiffSmooth_proof
    diffMagFromSup_proof comparisonExpConv_proof

end UnforcedLeray.Short.PartIIIb.Concrete

end
