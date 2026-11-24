import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.NewtonCurlRepSliceAE
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.NewtonCurlSliceDecay
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.NewtonCurlTimeComm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.L0TSliceBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.RealCCurlSliceDerivBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.CutoffSmulDeriv1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.CutoffSmulDeriv23
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.CurlCutoffTimeComm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.CurlCutoffL0TDiff
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.UniformCutoffLimitSliceTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.UniformCutoffLimitPairing
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/2`: the solution approximation `L0TSolApprox` (assembly)

Source `the November 2 reference manuscript` lines 119-120, 1356-1366,
1446-1455, 1464-1466.  Assembly only: `l0TSolApprox_of_fine` (compiled in `Of.lean`) applied to
the accepted leaves.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem l0TSolApprox : L0TSolApprox :=
  SolApprox.l0TSolApprox_of_fine SolApprox.newtonCurlRepSliceAE SolApprox.newtonCurlSliceDecay
    SolApprox.newtonCurlTimeComm SolApprox.l0TSliceBound SolApprox.realCCurlSliceDerivBound
    SolApprox.cutoffSmulDeriv1 SolApprox.cutoffSmulDeriv23 SolApprox.curlCutoffTimeComm
    SolApprox.curlCutoffL0TDiff SolApprox.uniformCutoffLimitSliceTest
    SolApprox.uniformCutoffLimitPairing

end UnforcedLeray.Short.PartIIIb.Concrete

end
