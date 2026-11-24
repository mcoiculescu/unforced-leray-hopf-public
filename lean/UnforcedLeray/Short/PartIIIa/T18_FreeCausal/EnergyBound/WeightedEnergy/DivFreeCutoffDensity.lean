import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimSmooth
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimDeriv
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPeriodic
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QL2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QMeanZero
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.PotentialFormulas
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.PotentialL2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.ScaledExists
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.CutPd
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.CutFlat
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.CutConverge

/-!
# Part III-a, task `PartIII-a:T18/3/1/1` (`DivFreeCutoffDensity`): assembly

Pure assembly of the eleven accepted lemma theorems (`QPrimSmooth`, `QPrimDeriv`, `QPeriodic`,
`QL2`, `QMeanZero`, `PotentialFormulas`, `PotentialL2`, `ScaledExists`, `CutPd`, `CutFlat`,
`CutConverge`) through the reductions `divFreeCutoffDensity_of`, `dfcPotentialExists_of` and
`dfcCutoffFromPotential_of` proved in `Sub/T18_3_1_1.lean`.

Source of record: `the November 2 reference manuscript`, lines 3541-3552.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem divFreeCutoffDensity : DivFreeCutoffDensity :=
  divFreeCutoffDensity_of
    (dfcPotentialExists_of dfcQMeanZero dfcPotentialFormulas dfcPotentialL2)
    (dfcCutoffFromPotential_of dfcScaledExists dfcCutFlat dfcCutConverge)

end UnforcedLeray.Short.IIIa

end
