import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3.Reduction
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3_1

/-!
# `SmoothForcePairing` (task `PartIII-b:C/flatset/col/7/1/1/3`)

Source of record `the November 2 reference manuscript` 1684-1689.
Assembles `smoothForcePairing_of` (`Reduction.lean`) with `smoothRepPairing`
(`PartIII-b_C_flatset_col_7_1_1_3_1.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem smoothForcePairing : SmoothForcePairing :=
  smoothForcePairing_of smoothRepPairing

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
