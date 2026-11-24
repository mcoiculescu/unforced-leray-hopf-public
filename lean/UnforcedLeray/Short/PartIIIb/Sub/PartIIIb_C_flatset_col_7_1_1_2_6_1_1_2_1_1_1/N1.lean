import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N1.T0gSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N1.T0gPeriodic
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N1.T0gBand
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N1.T0gCgradBand
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N1.T0gGrad
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N1.T0gMem
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N1.T0gAe

/-!
# `T0adjGradGauss` (N1): assembly of the seven leaf proofs

Source `the November 2 reference manuscript`
lines 1640-1656. The statement is discharged by `t0adjGradGauss_of` (Sub file) from the seven
leaf proofs in the folder `N1/`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem t0adjGradGauss_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0adjGradGauss :=
  t0adjGradGauss_of t0gSmooth_proof t0gPeriodic_proof t0gBand_proof t0gGrad_proof t0gMem_proof
    t0gAe_proof t0gCgradBand_proof

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
