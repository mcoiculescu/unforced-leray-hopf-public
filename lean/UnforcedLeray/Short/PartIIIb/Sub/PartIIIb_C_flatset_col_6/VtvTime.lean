import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3.VtvSliceExpand
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3.VtvEtaStream
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3.VtvTimeFubini
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.VtvTimeIntegrable

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvTime : VtvTime :=
  vtvTime_of vtvSliceExpand vtvEtaStream vtvTimeIntegrable vtvTimeFubini

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

end
