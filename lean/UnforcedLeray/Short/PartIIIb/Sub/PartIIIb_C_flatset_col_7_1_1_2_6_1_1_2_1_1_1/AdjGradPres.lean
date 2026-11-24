import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem t0adjGradPres : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0adjGradPres :=
  t0adjGradPres_of t0adjGradGauss_proof gaussGradInClosure_proof

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
