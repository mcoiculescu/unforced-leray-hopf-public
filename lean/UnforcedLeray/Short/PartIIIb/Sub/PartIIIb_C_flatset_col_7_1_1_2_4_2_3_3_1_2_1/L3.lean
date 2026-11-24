import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_1_3.M1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_1_3.M2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- (b) two-derivative Morrey sup bound, assembled from the large-period estimate
(`morreyTwoDerivsLarge_proof`, M1) and the cell period reduction (`cellPeriodReduction_proof`, M2). -/
theorem morreyTwoDerivs_proof : MorreyTwoDerivs :=
  morreyTwoDerivs_of morreyTwoDerivsLarge_proof cellPeriodReduction_proof

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
