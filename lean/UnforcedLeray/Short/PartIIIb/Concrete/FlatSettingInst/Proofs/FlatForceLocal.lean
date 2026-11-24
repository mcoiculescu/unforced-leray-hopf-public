import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_2
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatBmatCont
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatTermCont
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatTermBound

/-!
# `FlatForceLocal` (task `PartIII-b:C/flatset/col/2`)

Source of record `the November 2 reference manuscript`: 4594-4608, 4963-4976, 4988.
Assembly of `flatForceLocal_of` (`Sub/PartIII-b_C_flatset_col_2.lean`) with the three leaves
`flatBmatCont`, `flatTermCont`, `flatTermBound`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatForceLocal : FlatForceLocal :=
  flatForceLocal_of flatBmatCont flatTermCont flatTermBound

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
