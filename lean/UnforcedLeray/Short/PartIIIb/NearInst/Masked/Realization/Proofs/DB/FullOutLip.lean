import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.Lin
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.Majorant
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2

/-!
# `FullOutLip` (`PartIII-b:C/near/masked/18/3/2`, source 1688-1689, 3916-3921)

Assembly of `FullOutLip` from `fullOutSubLin` (linearity of `fullOut` on box tensors),
`fullOutMajorant` (pointwise positive majorant) and `fullMajL2` (`L²` bound of the majorant),
through `fullOutOneBound_of` and `fullOutLip_of` of the imported Sub file.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

theorem fullOutLip : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FullOutLip :=
  fullOutLip_of fullOutSubLin (fullOutOneBound_of fullOutMajorant fullMajL2)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
