import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.Vanish
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.OffAxis

/-!
# Part II-b, task `PartII-b:G4/5/2/1` (`RingLiftJet`): assembly

Source of record: `the November 2 reference manuscript` lines 2360-2366, 2386-2387.
The locality leaf `ringLiftVanish` and the off-axis leaf `ringLiftOffAxis` are assembled by
`ringLiftJet_of` (`Sub/PartII-b_G4_5_2_1.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem ringLiftJet : UnforcedLeray.Short.IIb.RingLiftJet :=
  UnforcedLeray.Short.IIb.ringLiftJet_of ringLiftVanish ringLiftOffAxis

end UnforcedLeray.Short.IIb
