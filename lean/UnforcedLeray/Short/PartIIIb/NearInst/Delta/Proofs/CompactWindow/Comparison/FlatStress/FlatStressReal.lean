import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_3
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.GenericStressReal

/-!
# `PartIII-b:C/near/delta/8/2/3/3/2`: `FlatStressReal`

Source of record `the November 2 reference manuscript`,
1675-1679 (stress maps are real), 1655-1656 (`T_0 = R_0 P_0` real).

Proof: `flatStressReal_of` reduces `FlatStressReal` to `GenericStressReal`, which is proved as
`genericStressReal` in the imported module.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

/-- **Flat stress maps are real** (source 1675-1679 at `ε = 0`). -/
theorem flatStressReal : FlatStressReal :=
  flatStressReal_of genericStressReal

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
