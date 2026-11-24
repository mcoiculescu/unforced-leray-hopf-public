import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1_2.L2GrowthComp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1_2.L4ContDiffParam

/-!
# Joint smoothness of the Gaussian average (`T0gGaussParam`)

Source `the November 2 reference manuscript`
lines 1640-1656. The statement is obtained from the decomposition
`t0gGaussParam_proof_of` (polynomial growth of the parametric derivatives, `t0g_growthComp`,
and the generic parametric smoothness theorem, `t0g_contDiffParam`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

theorem t0gGaussParam_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gGaussParam :=
  UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.t0gGaussParam_proof_of
    t0g_growthComp t0g_contDiffParam

end
