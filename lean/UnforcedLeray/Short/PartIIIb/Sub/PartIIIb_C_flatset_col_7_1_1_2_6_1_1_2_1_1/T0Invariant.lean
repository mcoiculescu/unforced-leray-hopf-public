import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.AdjGradPres
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.ComplexAdjoint

/-!
# `T0SolenoidalInvariant` (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1/2/1/1`)

Source `the November 2 reference manuscript`
1640-1656. The adjoint preserves the gradient closure (`t0adjGradPres`) and the complex
adjoint identity (`t0_complex_adjoint`); together they give the solenoidal invariance through
`t0SolenoidalInvariant_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem t0SolenoidalInvariant : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0SolenoidalInvariant :=
  t0SolenoidalInvariant_of t0_complex_adjoint t0adjGradPres

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
