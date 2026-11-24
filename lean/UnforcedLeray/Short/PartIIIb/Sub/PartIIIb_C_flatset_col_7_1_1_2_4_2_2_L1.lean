import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1.HasDerivDir
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1.Differentiable

/-!
# `SFCHeatCommute` (source 3426-3430): assembly of directional derivatives and differentiability

Source `the November 2 reference manuscript`
3426-3430. `sfcHeatHasDerivDir` (directional derivatives, `HasDerivDir.lean`) and
`sfcHeatDifferentiable` (`Differentiable.lean`) feed `sfcHeatCommute_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcHeatCommute : SFCHeatCommute :=
  sfcHeatCommute_of sfcHeatHasDerivDir sfcHeatDifferentiable

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
