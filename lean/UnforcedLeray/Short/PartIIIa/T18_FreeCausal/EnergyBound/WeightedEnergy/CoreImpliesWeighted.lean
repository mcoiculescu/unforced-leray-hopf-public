import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_1_4
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted.EnergyLocInt
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted.CoreToSmooth
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted.SmoothToC1

/-!
# Part III-a, `PartIII-a:T18/3/1/4`: `CoreImpliesWeighted`

Source of record: `the November 2 reference manuscript`, lines 3541-3552 and 3427-3440.

Assembly of the three lemmas `PartIII-a:T18/3/1/4/1` (`energyLocIntegrable`),
`PartIII-a:T18/3/1/4/2` (`coreToSmoothWeighted`) and `PartIII-a:T18/3/1/4/3` (`smoothToC1Weighted`)
through `coreImpliesWeighted_of`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **`PartIII-a:T18/3/1/4`**: `CoreAll` implies the weighted energy identity for `C¹` weights. -/
theorem coreImpliesWeighted : UnforcedLeray.Short.IIIa.CoreImpliesWeighted :=
  coreImpliesWeighted_of energyLocIntegrable coreToSmoothWeighted smoothToC1Weighted

end UnforcedLeray.Short.IIIa
