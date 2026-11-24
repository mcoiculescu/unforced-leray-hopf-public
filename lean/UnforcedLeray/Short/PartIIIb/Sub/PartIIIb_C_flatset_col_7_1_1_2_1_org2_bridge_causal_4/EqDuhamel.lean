import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal_4.P1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal_4.P2

/-!
# `CausalEqDuhamel` from the two analytic leaves

Assembly: `causalEqDuhamel := causalEqDuhamel_of planeHeatVecAe duhamelIntegrable`, with the
leaf `PlaneHeatVecAe` proved in `P1.lean` and the leaf `DuhamelIntegrable` proved in `P2.lean`.
Source `shorter-proof-2026-11-02.tex` 1650-1656, 1684-1689.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem causalEqDuhamel : CausalEqDuhamel :=
  causalEqDuhamel_of planeHeatVecAe duhamelIntegrable

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
