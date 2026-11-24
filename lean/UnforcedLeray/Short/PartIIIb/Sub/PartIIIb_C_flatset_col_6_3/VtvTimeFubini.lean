import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvDerivCyl
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvFubiniJoint
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvFubiniInner

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvTimeFubini : VtvTimeFubini :=
  vtvTimeFubini_of vtvDerivCyl vtvFubiniJoint vtvFubiniInner

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

end
