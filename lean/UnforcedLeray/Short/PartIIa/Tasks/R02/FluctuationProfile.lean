import UnforcedLeray.Short.PartIIa.Sub.R02_2
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.IterComm
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.KExpansion
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ProfileDict
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.SliceJetBound
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ExpPowAbsorb
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.FluctProfileSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff

/-!
# Part II-a, task `PartII-a:R02/2`: the late fluctuation profile bounds

Proves `LateFluctuationProfile` (`Sub/R02.lean`, line 245) from `TrainFluctuationDecay` and the
profile smoothness `LateProfileSmooth` (`Sub/R02.lean`, line 233).

Source of record: `the November 2 reference manuscript`, lines 439-446
(`sct:fluctuation`) and 1259-1276 (the late residual table).

The proof is the conditional assembly `lateFluctuationProfile_of_sub` (`Sub/R02_2.lean`) applied to
the calculus leaves in `Tasks/R02/FluctuationProfile/`:

* `fluctProfileSmooth_of` (smoothness of the stream fluctuation), with `hmeanContDiff`
  (horizontal averaging preserves smoothness, `Short/PartI/Tasks/TrainMeanEquations/`);
* `kExpansion_of profileIterComm` (expansion of `K^ℓ`);
* `profileIterComm` (commutation of the profile partials);
* `profileDict` (profile partials are nested slice derivatives);
* `sliceJetBound_of profileDict` (nested slice derivatives are bounded by jets);
* `expPowAbsorb` (absorbing a power of the age into the exponential).

Every hypothesis of the assembly is discharged by a proved leaf, so the statement below uses only
its two hypotheses `hF` and `hS`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R02/2`**: the late fluctuation profile bounds, from the fluctuation decay
`TrainFluctuationDecay` and the profile smoothness `LateProfileSmooth`. -/
theorem lateFluctuationProfile_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hS : UnforcedLeray.Short.PartIIa.LateProfileSmooth) :
    UnforcedLeray.Short.PartIIa.LateFluctuationProfile :=
  lateFluctuationProfile_of_sub hF hS
    (fluctProfileSmooth_of hS UnforcedLeray.Short.PartI.hmeanContDiff)
    (kExpansion_of profileIterComm) profileIterComm profileDict (sliceJetBound_of profileDict)
    expPowAbsorb

end UnforcedLeray.Short.PartIIa
