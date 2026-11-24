import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Duhamel
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge.Lift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge.Transfer
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal.Causal

/-!
# `DuhamelBridge` assembled from the three bridge leaves

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
Instantiates `duhamelBridge_of` with `bridgeLift` (Lift.lean), `bridgeCausal` (causal folder,
Causal.lean) and `bridgeTransfer` (Transfer.lean).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem duhamelBridge : DuhamelBridge :=
  duhamelBridge_of bridgeLift bridgeCausal bridgeTransfer

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
