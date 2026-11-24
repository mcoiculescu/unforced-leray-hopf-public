import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_1_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_1_3

/-!
# `SmoothForceDense` (`PartIII-b:C/flatset/col/7/1/1/1`)

Assembly of the three source facts `sfdTrunc`, `sfdSmoothApprox`, `sfdPeriodize` through
`smoothForceDense_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem smoothForceDense : SmoothForceDense :=
  smoothForceDense_of sfdTrunc sfdSmoothApprox sfdPeriodize

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
