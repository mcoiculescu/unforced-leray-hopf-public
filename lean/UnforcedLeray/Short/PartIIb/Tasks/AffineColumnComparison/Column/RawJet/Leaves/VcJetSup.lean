import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup.AgeJetLe
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup.SpatialJetBound

/-!
Task `PartII-b:G4/3/6/1/5` (`VcJetSup`): `VcJetSup` from the two jet facts
`vcAgeJetLe_proof` (task `PartII-b:G4/3/6/1/5/1`, `VcJetSup/AgeJetLe.lean`) and
`vcSpatialJetBound_proof` (task `PartII-b:G4/3/6/1/5/2`, `VcJetSup/SpatialJetBound.lean`)
via `vcJetSup_of` (`Sub/PartII-b_G4_3_6_1_5.lean`, SP 2205).
-/

namespace UnforcedLeray.Short.IIb

theorem vcJetSup_proof : UnforcedLeray.Short.IIb.VcJetSup :=
  vcJetSup_of vcAgeJetLe_proof vcSpatialJetBound_proof

end UnforcedLeray.Short.IIb
