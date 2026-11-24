import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1.N1.T0gSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1.L1Bdd

/-!
# Gradient of `Ψ` (`T0gGrad`)

Source `the November 2 reference manuscript`
lines 1640-1656. The statement is assembled from `t0gGrad_of` (differentiation of the heat flow
under the Gaussian integral, with inputs `t0gSmooth_proof` and `t0gBdd_proof`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem t0gGrad_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gGrad :=
  t0gGrad_of t0gSmooth_proof t0gBdd_proof

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
