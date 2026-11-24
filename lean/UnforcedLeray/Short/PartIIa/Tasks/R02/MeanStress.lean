import UnforcedLeray.Short.PartIIa.Sub.R02_6
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.IterComm
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.KExpansion
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ProfileDict
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.SliceJetBound
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ExpPowAbsorb
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.AgeDerivSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.HmeanMulFluct
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.MeanStressSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.HmeanAgeIter
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.HmeanEtaDeriv
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.HmeanMixedDeriv
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.MixedLeibniz
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.FluctVelSliceBound
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.MeanStressIntegrandBound
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.MeanStressDerivForm
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanDerivS

/-!


Proves `LateMeanStress` (`Sub/R02.lean`, line 304) from `TrainFluctuationDecay` (`sct:fluctuation`,
source `the November 2 reference manuscript` lines 439-446), `TrainMeanEquations`
(`sct:mean`, lines 397-404) and the late residual table (lines 1259-1276).

The proof is the assembly `lateMeanStress_of_sub` (`Sub/R02_6.lean`) applied to the leaf
theorems in `Tasks/R02/FluctuationProfile/` and `Tasks/R02/MeanStress/`, together with
`hmeanContDiff` and `hmeanDerivS` from `Short/PartI/Tasks/TrainMeanEquations/`.
The hypothesis `hS` is not used: it is kept so that the statement is exactly the target.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R02/6`**: the late mean-stress bounds, from the fluctuation decay and the mean
equations (`sct:mean`, `sct:fluctuation`). The hypothesis `hS` is unused. -/
theorem lateMeanStress_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (hS : UnforcedLeray.Short.PartIIa.LateProfileSmooth) :
    UnforcedLeray.Short.PartIIa.LateMeanStress :=
  let hSm := meanStressSmooth_of UnforcedLeray.Short.PartI.hmeanContDiff
  let hMix := hmeanMixedDeriv_of ageDerivSmooth
    (hmeanAgeIter_of UnforcedLeray.Short.PartI.hmeanDerivS ageDerivSmooth) hmeanEtaDeriv
  lateMeanStress_of_sub (kExpansion_of profileIterComm) profileIterComm profileDict hSm
    (meanStressDerivForm_of hE hmeanMulFluct hMix hSm)
    (meanStressIntegrandBound_of (mixedLeibniz_of ageDerivSmooth)
      (fluctVelSliceBound_of hF (sliceJetBound_of profileDict) hSm) hSm expPowAbsorb)

end UnforcedLeray.Short.PartIIa
