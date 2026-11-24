import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_2

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem bodyColumnEnergy : BodyColumnEnergy :=
  bodyColumnEnergy_of bodyColumnSmoothSeq energyCauchyLimit

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
