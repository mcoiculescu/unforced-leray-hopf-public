import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem bodyColumnFlat : BodyColumnFlat :=
  bodyColumnFlat_of bodyColumnEnergy energyNullModification bodyColumnWeak

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
