import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3.FlatBSmall
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3.FlatBContinuous
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3.FlatGBSmall
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3.FlatXiSmall
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3.FlatXiContinuous
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves

/-!
# `flatXiRegular : FlatXiRegular` (decomposition of `PartIII-b:C/flatset/col/3`, assembly)

Source of record `the November 2 reference manuscript` lines 4610, 4614-4615.
Assembles `flatXiRegular_of` from the five leaf theorems `flatBSmall`, `flatBContinuous`,
`flatGBSmall`, `flatXiSmall`, `flatXiContinuous`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatXiRegular : FlatXiRegular :=
  flatXiRegular_of flatBSmall flatBContinuous flatGBSmall flatXiSmall flatXiContinuous

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
