import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2.VtvFubiniMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2.VtvFubiniOpBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2.VtvDerivBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvDerivCyl

/-!
# `PartIII-b:C/flatset/col/6/3/4/2` (`vtvFubiniJoint`): joint Fubini assembly

The joint statement follows from `vtvFubiniJoint_of` applied to the four leaves
`vtvDerivCyl`, `vtvFubiniMeas`, `vtvFubiniOpBound`, `vtvDerivBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvFubiniJoint : VtvFubiniJoint :=
  vtvFubiniJoint_of vtvDerivCyl vtvFubiniMeas vtvFubiniOpBound vtvDerivBound

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

end
