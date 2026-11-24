import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4_3.Rep
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4_3.Weak
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4_3.Slice

/-!
# `KcGradient` (decomposition of `PartIII-b:C/flatset/col/4/3`, assembly)

Source of record `the November 2 reference manuscript` 3426-3430, 3236-3240.
The three leaves `kcGradRep`, `kcGradWeak`, `kcGradSlice` (files `Rep.lean`, `Weak.lean`,
`Slice.lean` of `PartIII-b_C_flatset_col_4_3`) feed `kcGradient_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `KcGradient` from the three leaves. -/
theorem kcGradient : KcGradient :=
  kcGradient_of kcGradRep kcGradWeak kcGradSlice

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
