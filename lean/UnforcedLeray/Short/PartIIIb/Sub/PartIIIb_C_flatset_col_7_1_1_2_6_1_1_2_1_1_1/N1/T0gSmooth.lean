import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1.L4Assemble
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1.L1Bdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1.L2GaussParam
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1.L3HeatSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N1.T0gBand

/-!
# Smoothness of `Ψ` (`T0gSmooth`)

Source `the November 2 reference manuscript`
lines 1640-1656. The statement is assembled from `t0gSmooth_of` (band plus smoothness on
`{s > 0}`), `t0gBand_proof` (band support), and `t0gHeatPos_of_parts` fed with the leaf proofs
`t0gBdd_proof`, `t0gGaussParam_proof`, `t0gHeatSub_proof`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

theorem t0gSmooth_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gSmooth :=
  t0gSmooth_of t0gBand_proof
    (t0gHeatPos_of_parts t0gBdd_proof t0gGaussParam_proof t0gHeatSub_proof)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
