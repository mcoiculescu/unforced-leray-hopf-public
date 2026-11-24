import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal.GhRep
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal.MsEq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal.SliceAe
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal_4.EqDuhamel

/-!
# `BridgeCausal` from four leaves

Source `the November 2 reference manuscript`
1650-1656, 1684-1689.  Assembles `bridgeCausal_of` from the four leaf theorems
`causalGhRep` (GhRep.lean), `causalMsEq` (MsEq.lean), `causalSliceAe` (SliceAe.lean) and
`causalEqDuhamel` (the sibling folder `…_org2_bridge_causal_4/EqDuhamel.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem bridgeCausal : BridgeCausal :=
  bridgeCausal_of causalGhRep causalMsEq causalSliceAe causalEqDuhamel

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
