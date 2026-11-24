import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_5

/-!
# `FlatForceCurl` (task `PartIII-b:C/flatset/col/1`)

Assembly of the four leaves `flatForceSmooth` (`Sub/PartIII-b_C_flatset_col_1_2.lean`),
`flatForcePeriodic` (`Sub/PartIII-b_C_flatset_col_1_3.lean`), `flatForceCurlTsum`
(`Sub/PartIII-b_C_flatset_col_1_4.lean`) and `flatForceGB` (`Sub/PartIII-b_C_flatset_col_1_5.lean`)
through `flatForceCurl_of` (`Sub/PartIII-b_C_flatset_col_1.lean`).
Source of record `the November 2 reference manuscript`: 4594-4608, 4963-4976, 4988.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatForceCurl : FlatForceCurl :=
  flatForceCurl_of flatForceSmooth flatForcePeriodic flatForceCurlTsum flatForceGB

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
