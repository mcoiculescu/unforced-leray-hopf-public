import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_2

/-!
# `SFCDiv` (`PartIII-b:C/flatset/col/7/1/1/2/6`)

Assembly of the two source facts `sfcDivAE` (a.e. slice divergence identity) and `sfcDivCont`
(continuity of the slice pairing on `s > 0`) through `sfcDiv_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcDiv : SFCDiv :=
  sfcDiv_of sfcDivAE sfcDivCont

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
