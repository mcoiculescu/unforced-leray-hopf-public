import UnforcedLeray.Short.PartI.Sub.PartI_T23_2
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansion.RemainderLpBound.StreamDuhamel
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansion.RemainderLpBound.DatumRemainderBound
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansion.RemainderLpBound.SourceRemainderBound

/-!
# `TrainMeanRemainderLpBound` (`PartI:T23/2`)

Source of record: `the November 2 reference manuscript`, lines 448-459 and
528-539, in the proof of Lemma `sct:expansion`.

The unconditional infrastructure and decomposition for `PartI:T23/2` are established in
`UnforcedLeray.Short.PartI.Sub.PartI_T23_2`, which proves:
* `PartI_T23.eLpNorm_pow_mul_le_of_pointwise`
* `PartI_T23.heatKernel1_weighted_jet_bound`
* `PartI_T23.meanCoeff_bound_of_fluctDecay`
* `PartI_T23.meanStress_weighted_jet_decay_of_fluctDecay`
* `PartI_T23.meanDatumDuhamel_eq_vortexMeanStream`
* `PartI_T23.meanRemainder_slice_eq_add_of_duhamel`
* `trainMeanRemainderPointwiseBound_of`
* `trainMeanRemainderLpBound_of`
* `trainMeanRemainderPointwiseBound_of_lp`
* `trainMeanRemainderLpBound_of_leaves`
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- Pointwise weighted Taylor remainder bound for `meanRemainder` (`PartI:T23/2`), assembled from
the three leaf theorems `trainMeanStreamDuhamel_proof` (`PartI:T23/2/1`),
`trainMeanDatumRemainderBound_proof` (`PartI:T23/2/2`), and `trainMeanSourceRemainderBound_proof`
(`PartI:T23/2/3`). -/
theorem trainMeanRemainderPointwiseBound_proof
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : TrainFluctuationDecay)
    (hMP : OverlapMeanPrimitive) :
    TrainMeanRemainderPointwiseBound :=
  trainMeanRemainderPointwiseBound_of
    (trainMeanStreamDuhamel_proof hTails hFD hMP)
    (trainMeanDatumRemainderBound_proof hTails)
    (trainMeanSourceRemainderBound_proof hTails hFD hMP)

/-- **Main theorem (`PartI:T23/2`)**: `L^p` Taylor remainder bound for the 1D heat Duhamel
expansion of `meanStream` (`sct:expansion`, source lines 448-459 and 528-539). -/
theorem trainMeanRemainderLpBound_proof (hTails : TrainStreamVelocityPressureTails) (hFD : TrainFluctuationDecay) (hMP : OverlapMeanPrimitive) : TrainMeanRemainderLpBound :=
  trainMeanRemainderLpBound_of_leaves
    (trainMeanStreamDuhamel_proof hTails hFD hMP)
    (trainMeanDatumRemainderBound_proof hTails)
    (trainMeanSourceRemainderBound_proof hTails hFD hMP)

end UnforcedLeray.Short.PartI

