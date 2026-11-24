import UnforcedLeray.Short.PartIIa.Sub.R02_3
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.IterComm
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.KExpansion
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ProfileDict
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.AgeDerivSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.HeatKernelIterSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.MeanRemainderSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.SliceDerivContinuous
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.EssSupPointwise
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.MeanRemPointwise

/-!
# Part II-a, task `PartII-a:R02/3`: the late mean remainder bounds

Proves `LateMeanRemainder` (`Sub/R02.lean`, line 261) from the train expansion
`TrainMeanExpansion`, the train mean equations `TrainMeanEquations`, and the profile smoothness
`LateProfileSmooth` (`Sub/R02.lean`, line 233).

Source of record: `the November 2 reference manuscript`, lines 447-459
(`sct:expansion`) and 1259-1276 (the late residual table).

The proof is the conditional assembly `lateMeanRemainder_of_sub` (`Sub/R02_3.lean`) applied to
the calculus leaves in `Tasks/R02/FluctuationProfile/` and `Tasks/R02/MeanRemainder/`:

* `kExpansion_of profileIterComm` (expansion of `K^ℓ`);
* `profileIterComm` (commutation of the profile partials);
* `profileDict` (profile partials are nested slice derivatives);
* `meanRemainderSmooth_of hE heatKernelIterSmooth` (joint smoothness of `R_N` for `s > 0`);
* `meanRemPointwise_of hM hSm (sliceDerivContinuous_of ageDerivSmooth) essSupPointwise`
  (the `p = ∞` case of `TrainMeanExpansion`, read pointwise).

The hypothesis `hS : LateProfileSmooth` is not used by this proof; it is kept in the signature so
that the statement is exactly the target.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R02/3`**: the late mean remainder bounds, from the train expansion
`TrainMeanExpansion`, the train mean equations `TrainMeanEquations` and the profile smoothness
`LateProfileSmooth`. -/
theorem lateMeanRemainder_of (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (hS : UnforcedLeray.Short.PartIIa.LateProfileSmooth) :
    UnforcedLeray.Short.PartIIa.LateMeanRemainder :=
  let hSm := meanRemainderSmooth_of hE heatKernelIterSmooth
  lateMeanRemainder_of_sub (kExpansion_of profileIterComm) profileIterComm profileDict hSm
    (meanRemPointwise_of hM hSm (sliceDerivContinuous_of ageDerivSmooth) essSupPointwise)

end UnforcedLeray.Short.PartIIa
