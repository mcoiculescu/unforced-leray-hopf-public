import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.CutoffLimit
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.SliceLoc
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.NormSq
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.AgeSlice
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.YoungSlice
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.GainLocBG
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.GainLocF
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy

/-!
# Part III-a, task `PartIII-a:T18/3/2` (assembly): `FreeEnergyInequalities`

Applies `freeEnergyInequalities_of` (Sub/PartIII-a_T18_3_2.lean) to the seven scalar and
measure-theoretic leaves in `EnergyBound/Inequalities/*.lean` and to the unconditional weighted
energy identity `weightedEnergyIdentity` (EnergyBound/WeightedEnergy.lean).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem freeEnergyInequalities : UnforcedLeray.Short.IIIa.FreeEnergyInequalities :=
  UnforcedLeray.Short.IIIa.freeEnergyInequalities_of
    UnforcedLeray.Short.IIIa.cutoffLimit
    UnforcedLeray.Short.IIIa.sliceLoc
    UnforcedLeray.Short.IIIa.normSq
    UnforcedLeray.Short.IIIa.ageSlice
    UnforcedLeray.Short.IIIa.youngSlice
    UnforcedLeray.Short.IIIa.gainLocBG
    UnforcedLeray.Short.IIIa.gainLocF
    UnforcedLeray.Short.IIIa.weightedEnergyIdentity

end UnforcedLeray.Short.IIIa
