import UnforcedLeray.Short.PartI.Sub.PartI_T23_3
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansion.RemainderLpBound

/-!
# `TrainMeanStreamLpBound` (`PartI:T23/3`)

Source of record: `the November 2 reference manuscript`, lines 459-462 and
539-540, in the proof of Lemma `sct:expansion`:
"In particular, replacing the remainder power by `(m - b - 1)/2 - ℓ + 1/(2p)` bounds `S` itself
with `s` replaced by `1 + s`."

The unconditional infrastructure and conditional assembly for `PartI:T23/3` are established in
`UnforcedLeray.Short.PartI.Sub.PartI_T23_3`, which proves:
* `PartI_T23.trainInteriorStripJetBounds_of_tails`
* `PartI_T23.iteratedDeriv_slice_add`
* `PartI_T23.meanStream_pointwise_bound_pos_le_one`
* `PartI_T23.meanStream_pointwise_bound_ge_one_of_remainder`
* `PartI_T23.meanStream_pointwise_bound_zero_age_zero_deriv`
* `PartI_T23.trainMeanStreamZeroAgeDerivBound_of_tails`
* `trainMeanStreamPointwise_of`
* `trainMeanStreamLpBound_of`
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Main theorem (`PartI:T23/3`)**: `L^p` bound for `meanStream` and its age-vertical derivatives
(`sct:expansion`, source lines 459-462 and 539-540). -/
theorem trainMeanStreamLpBound_proof (hTails : TrainStreamVelocityPressureTails) (hFD : TrainFluctuationDecay) (hMP : OverlapMeanPrimitive) : TrainMeanStreamLpBound :=
  trainMeanStreamLpBound_of hTails hFD hMP (trainMeanRemainderLpBound_proof hTails hFD hMP)

end UnforcedLeray.Short.PartI

