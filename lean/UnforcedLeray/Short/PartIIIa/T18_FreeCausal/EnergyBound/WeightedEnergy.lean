import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted

/-!
# Part III-a, task `PartIII-a:T18/3/1` (assembly): the unconditional weighted energy identity

Assembles the four leaf theorems `divFreeCutoffDensity`, `flatWeakFromDensity`, `lionsMagenesCyl`,
`coreImpliesWeighted` through `weightedEnergyIdentity_of` (Sub/T18_3_1.lean).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem weightedEnergyIdentity : UnforcedLeray.Short.IIIa.WeightedEnergyIdentity :=
  weightedEnergyIdentity_of divFreeCutoffDensity flatWeakFromDensity lionsMagenesCyl coreImpliesWeighted

end UnforcedLeray.Short.IIIa
