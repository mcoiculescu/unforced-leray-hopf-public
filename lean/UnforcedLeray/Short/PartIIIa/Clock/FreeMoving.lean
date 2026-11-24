import UnforcedLeray.Short.PartIIIa.Sub.T21_c2
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Scale
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Gronwall

/-!
# Part III-a, task `PartIII-a:T21/c2`: `FreeMovingEnergy`

Source of record: `the November 2 reference manuscript`, lines 2937-2958.
Assembles `freeMovingEnergy : FreeMovingEnergy` from `freeMovingEnergy_of`, `fmeScale`,
`fmeRate`, and `fmeGronwall`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem freeMovingEnergy : FreeMovingEnergy :=
  freeMovingEnergy_of fmeScale fmeRate fmeGronwall

end UnforcedLeray.Short.IIIa
