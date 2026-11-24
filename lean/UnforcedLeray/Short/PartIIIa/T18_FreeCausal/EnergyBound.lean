import UnforcedLeray.Short.PartIIIa.Sub.T18_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities

/-!
# Part III-a, task `PartIII-a:T18/3`: the free a priori energy bounds

Source of record: `the November 2 reference manuscript`, lines 3427-3440 and
3541-3552. The conditional arithmetic is `freeCausalEnergyBound_of` (`Sub/T18_3.lean`), applied to
the unconditional `freeEnergyInequalities` (`EnergyBound/Inequalities.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem freeCausalEnergyBound : UnforcedLeray.Short.IIIa.FreeCausalEnergyBound :=
  freeCausalEnergyBound_of freeEnergyInequalities

end UnforcedLeray.Short.IIIa
