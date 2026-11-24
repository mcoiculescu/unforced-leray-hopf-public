import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.VtvTimeSupport
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.VtvBandL1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.VtvFSlice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.VtvTestBounds
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.VtvYPairBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.VtvRPairBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.VtvYRMeas

/-!
# `VtvTimeIntegrable` from the leaves (source 4610, 3511-3514)

Assembles `vtvTimeIntegrable_of` from the seven leaf theorems.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvTimeIntegrable : VtvTimeIntegrable :=
  vtvTimeIntegrable_of vtvTimeSupport vtvBandL1 vtvFSlice vtvTestBounds vtvYPairBound
    vtvRPairBound vtvYRMeas

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
