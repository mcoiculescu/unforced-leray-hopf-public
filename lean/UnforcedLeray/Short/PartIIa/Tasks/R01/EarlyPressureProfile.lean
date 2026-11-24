import UnforcedLeray.Short.PartIIa.Sub.R01_2
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.IterComm
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ProfileDict
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.SliceJetBound

/-!
# Part II-a, task `PartII-a:R01/2`: the zero-age pressure profile

Source of record: `the November 2 reference manuscript`, lines 439-446
(`sct:fluctuation`, third component: the decaying-gauge pressure itself), at ages `0 < s ≤ 1`.

`earlyPressureProfile_of` is the unconditional statement.  It is the conditional theorem
`earlyPressureProfile_of_sub` (`Sub/R01_2.lean`, from `TrainFluctuationDecay`, `LateProfileSmooth`
and the three profile-calculus leaves `ProfileIterComm`, `ProfileDict`, `SliceJetBound` of
`Sub/R02_2.lean`) applied to the proofs of those leaves in `Tasks/R02/FluctuationProfile/`:
`profileIterComm`, `profileDict`, and `sliceJetBound_of profileDict`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R01/2`** (source lines 439-446): the zero-age bounds for every mixed jet
`∂_s^ℓ ∂_η^a ∂_q^b p` of the pressure profile of an exact train, from the Part I fluctuation decay
and the smoothness of the profiles. -/
theorem earlyPressureProfile_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hS : LateProfileSmooth) : EarlyPressureProfile :=
  earlyPressureProfile_of_sub profileIterComm profileDict (sliceJetBound_of profileDict) hF hS

end UnforcedLeray.Short.PartIIa
