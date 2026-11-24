import UnforcedLeray.Short.PartIIa.Sub.R01_1
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyStreamProfile.JetAdd
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyStreamProfile.MeanStreamSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.IterComm
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ProfileDict
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.SliceJetBound
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.AgeDerivSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.SliceDerivContinuous
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.EssSupPointwise

/-!
# Part II-a, task `PartII-a:R01/1`: the zero-age stream profile (assembly)

Source of record: `the November 2 reference manuscript`, lines 439-459
(`sct:fluctuation`, `sct:expansion`), read at ages `0 < s ≤ 1`, and lines 1294-1297 ("at zero
age the integrands are bounded").

Target: `earlyStreamProfile_of`. It assembles the conditional theorem `earlyStreamProfile_of_sub`
(`Sub/R01_1.lean`) from its proved leaves: `profileIterComm`, `profileDict`, `sliceJetBound_of`,
`profileJetAdd`, `meanStreamSmooth_of`, `sliceDerivContinuous_of`, `ageDerivSmooth`,
`essSupPointwise`. No hypotheses are added beyond the target's.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- The zero-age stream profile, from the fluctuation decay, the mean expansion and the late
profile smoothness. -/
theorem earlyStreamProfile_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion) (hS : LateProfileSmooth) :
    EarlyStreamProfile :=
  earlyStreamProfile_of_sub profileIterComm profileDict (sliceJetBound_of profileDict)
    profileJetAdd (meanStreamSmooth_of hS) (sliceDerivContinuous_of ageDerivSmooth)
    essSupPointwise hF hM hS

end UnforcedLeray.Short.PartIIa
