import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_6.Final

/-!
# Part II-b, task `PartII-b:T22/2/3/1/6` (`LocStep`)

Source: `the November 2 reference manuscript`, lines 2100-2105 and
2085-2093 (the local step of the backward route on the cylinder).

The statement is discharged by the organizer's proof `LS.locStep_proved` in
`Short/PartII-b/Sub/PartIIb_T22_2_3_1_6/Final.lean`, which is compiled and
axiom-clean (propext, Classical.choice, Quot.sound).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb.BwdRoute

theorem locStep : UnforcedLeray.Short.IIb.BwdRoute.LocStep := LS.locStep_proved

end UnforcedLeray.Short.IIb.BwdRoute
