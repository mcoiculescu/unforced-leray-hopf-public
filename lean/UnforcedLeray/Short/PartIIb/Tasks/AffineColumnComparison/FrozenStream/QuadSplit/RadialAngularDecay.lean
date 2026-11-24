import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RadOne.RadOneDDecay

/-!
# Part II-b, task `PartII-b:G4/2/2/4`: `radialAngularDecay`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Composition: `radialAngularDecay_of` (Sub/PartIIb_G4_2_2_4) reduces `RadialAngularDecay` to
`RadOneDDecay`, which is proved by the leaf `radOneDDecay` (RadOne/RadOneDDecay).
-/

set_option autoImplicit false

noncomputable section

theorem radialAngularDecay : UnforcedLeray.Short.IIb.RadialAngularDecay :=
  UnforcedLeray.Short.IIb.radialAngularDecay_of radOneDDecay
