import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.WeakH1Exists.H1Volterra

/-!
# Leaf 1 (`PartII-b:F8/1/org/2/1`): `RealCylOseenWeakH1Exists`

Proves `RealCylOseenWeakH1Exists` by assembling the solenoidal `H¹_σ(C_c)` Volterra mild/weak
evolution constructed in `WeakH1Exists/ShiftAvg.lean` and `WeakH1Exists/H1Volterra.lean`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem realCylOseenWeakH1Exists_proof : UnforcedLeray.Short.IIb.RealCylOseenWeakH1Exists :=
  F8WeakEx.realCylOseenWeakH1Exists

end UnforcedLeray.Short.IIb
