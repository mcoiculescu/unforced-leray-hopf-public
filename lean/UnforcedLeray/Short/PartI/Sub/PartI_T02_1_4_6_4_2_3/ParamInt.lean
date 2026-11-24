import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2.L1
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2.L2
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2.L3
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2.L4
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2.L5

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Short.PartI

theorem leafParamIntCH_proof : UnforcedLeray.Short.PartI.LeafParamIntCH :=
  leafParamIntCH_of leafCellTestPartialCH_proof leafParamIntIntegrableCH_proof
    leafParamIntBoundedCH_proof leafParamIntHasFDerivCH_proof leafVecLaplacianPartialsCH_proof
