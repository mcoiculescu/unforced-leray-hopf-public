import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1.DilStrong
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1.HeatStrong

set_option autoImplicit false

theorem t0_strong_cont_zero : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0StrongContZero :=
  UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.t0_strong_cont_zero_of
    (fun c g => tendsto_dilH_exp_neg_zero c g)
    (fun c ν hc g => UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.tendsto_heatH_heatTime_zero c ν hc g)
