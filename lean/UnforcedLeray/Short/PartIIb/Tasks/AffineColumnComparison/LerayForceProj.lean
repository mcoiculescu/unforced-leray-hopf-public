import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.LerayForceProj.LerayYq
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_2

/-!
# `LerayForceProj` from `LerayYq` (`PartII-b:G4/4/2`)

Source: `the November 2 reference manuscript` line 2383 (with 2370-2383, 119-120,
1307-1308). `lerayForceProj_of` (in `Sub/PartII-b_G4_4_2.lean`) derives `LerayForceProj` from
`LerayYq`, and `lerayYq` (task `PartII-b:G4/4/2/1`) proves `LerayYq` with no hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Leray projection onto the force space** (SP 2383), proved from `LerayYq`. -/
theorem lerayForceProj : UnforcedLeray.Short.IIb.LerayForceProj :=
  lerayForceProj_of lerayYq

#print axioms lerayForceProj

end UnforcedLeray.Short.IIb
