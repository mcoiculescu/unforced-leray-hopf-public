import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_6.Mild

/-!


Source: `the November 2 reference manuscript`, lines 2085-2093 and 2100-2105.
`LocStep` follows from `locStep_of` (`Sub/PartIIb_T22_2_3_1_6.lean`) and its seven leaves, all proved
in this folder (`Gains.lean`, `Mild.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb.BwdRoute

namespace LS

/-- **`LocStep`**: one order of local regularity is gained on a band three units narrower. -/
theorem locStep_proved : LocStep :=
  locStep_of truncDrift freeCB gLinear gainZero gainOne commGain classicalToMild

end LS

end UnforcedLeray.Short.IIb.BwdRoute

#print axioms UnforcedLeray.Short.IIb.BwdRoute.LS.locStep_proved
