import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit

/-!
# Part III-a, task `PartIII-a:T18/3/1/3` (`LionsMagenesCyl`): the assembly file

The unconditional theorem `lionsMagenesCyl` is the composition of the three proved parts of the
split `Sub/T18_3_1_3.lean`:

* (a) `UnforcedLeray.Short.IIIa.hasLMMollifier` (`LionsMagenesCyl/Mollifier.lean`);
* (b) `mollifiedEnergyIdentity` (`LionsMagenesCyl/MollIdentity.lean`);
* (c) `UnforcedLeray.Short.IIIa.mollifiedEnergyLimit` (`LionsMagenesCyl/MollLimit.lean`).

Each is fed to `lionsMagenesCyl_of_split`. The definitions are not repeated here; they live only in
`Sub/T18_3_1_3.lean`. Source of record:
`the November 2 reference manuscript`, lines 3427-3440 and 3541-3552.
-/

set_option autoImplicit false

theorem lionsMagenesCyl : UnforcedLeray.Short.IIIa.LionsMagenesCyl :=
  UnforcedLeray.Short.IIIa.lionsMagenesCyl_of_split UnforcedLeray.Short.IIIa.hasLMMollifier
    mollifiedEnergyIdentity UnforcedLeray.Short.IIIa.mollifiedEnergyLimit
