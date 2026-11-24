import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.SmoothWeak
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.L2Sq
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.L2SqT
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.Pair
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.Twice
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.PointwiseE
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.PointwiseN
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.PointwiseR
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.DomEN
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.DomR
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.MeasEN
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.MeasR
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.AeGood
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.LocInt
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.DCT

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3` (`MollLimit`): the limit `k → ∞` of the mollified identity

Source of record: `the November 2 reference manuscript` lines 3427-3440 (energy
class) and 3541-3552 (energy identity, limit `k → ∞`).

Assembly: `MollifiedEnergyLimit` is `mollifiedEnergyLimit_of` (`Sub/T18_3_1_3_3.lean`) applied to
the fifteen proved Props from the `MollLimit/` folder.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **The limit of the mollified identity** (SP 3541-3552, `k → ∞`): the mollified energy
identity converges to the energy identity for the energy class. Assembled from the proved Props. -/
theorem mollifiedEnergyLimit : UnforcedLeray.Short.IIIa.MollifiedEnergyLimit :=
  mollifiedEnergyLimit_of lmMollPointwiseE lmMollPointwiseN (lmMollPointwiseR lmSmoothWeakPd)
    lmMollDomEN (lmMollDomR lmSmoothWeakPd) (lmMollMeasurableEN lmAeGoodSlice)
    (lmMollMeasurableR lmSmoothWeakPd lmAeGoodSlice) lmAeGoodSlice lmEnergyLocInt lmWeightedDCT

end UnforcedLeray.Short.IIIa
