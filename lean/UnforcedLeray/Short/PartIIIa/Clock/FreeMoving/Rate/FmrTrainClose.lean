import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2.TrainClose
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails

/-!
# Part III-a, `PartIII-a:T21/c2/2/1`: `fmrTrainClose`

Source of record: `the November 2 reference manuscript` (SP), lines 2085-2090,
291-303, 463-467, 541-543.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Short.PartI

/-- **`FmrTrainClose`** from `PartI.TrainTransverseTails` and the unconditional
`PartI.trainComparison_proof` (SP lines 2085-2090, 291-303, 463-467, 541-543). -/
theorem fmrTrainClose_of_tails (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) :
    FmrTrainClose :=
  fmrTrainClose_of UnforcedLeray.Short.PartI.trainComparison_proof hT

/-- **`FmrTrainClose`** from `PartI.TrainVorticityGaussianTail` (`PartI:T20`) and
`PartI.TrainStreamVelocityPressureTails` (`PartI:T21`) via `PartI.trainTransverseTails_proof`
(`PartI:T24`). -/
theorem fmrTrainClose_conditional
    (hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail)
    (hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails) :
    FmrTrainClose :=
  fmrTrainClose_of UnforcedLeray.Short.PartI.trainComparison_proof
    (UnforcedLeray.Short.PartI.trainTransverseTails_proof hVort hTails)

/-- **`TrainOverlap`** assembled from `overlap_highnorm_uniform` (`PartI:T12`),
`trainOverlap_proof` (`PartI:T16`), and the conditional overlap tasks `PartI:T13`, `PartI:T14`,
`PartI:T15`. -/
theorem trainOverlap_of_parts
    (hFD : OverlapHighNormUniform → OverlapFluctuationDecay)
    (hMP : OverlapMeanPrimitive)
    (hMD : OverlapHighNormUniform → OverlapFluctuationDecay → OverlapMeanPrimitive → OverlapMeanDecay) :
    TrainOverlap :=
  trainOverlap_proof (hFD overlap_highnorm_uniform)
    (hMD overlap_highnorm_uniform (hFD overlap_highnorm_uniform) hMP)

/-- **`TrainTransverseTails`** assembled from `PartI:T12..T16`, `PartI:T20`, `PartI:T21`, and
`PartI:T24`. -/
theorem trainTransverseTails_of_parts
    (hFD : OverlapHighNormUniform → OverlapFluctuationDecay)
    (hMP : OverlapMeanPrimitive)
    (hMD : OverlapHighNormUniform → OverlapFluctuationDecay → OverlapMeanPrimitive → OverlapMeanDecay)
    (hVort : TrainOverlap → TrainVorticityGaussianTail)
    (hTails : TrainOverlap → TrainVorticityGaussianTail → TrainStreamVelocityPressureTails) :
    TrainTransverseTails :=
  let hOv := trainOverlap_of_parts hFD hMP hMD
  trainTransverseTails_proof (hVort hOv) (hTails hOv (hVort hOv))

/-- **`FmrTrainClose`** assembled from all Part I overlap and tail tasks (`PartI:T10`,
`PartI:T12..T16`, `PartI:T20`, `PartI:T21`, `PartI:T24`). -/
theorem fmrTrainClose_of_partI
    (hFD : OverlapHighNormUniform → OverlapFluctuationDecay)
    (hMP : OverlapMeanPrimitive)
    (hMD : OverlapHighNormUniform → OverlapFluctuationDecay → OverlapMeanPrimitive → OverlapMeanDecay)
    (hVort : TrainOverlap → TrainVorticityGaussianTail)
    (hTails : TrainOverlap → TrainVorticityGaussianTail → TrainStreamVelocityPressureTails) :
    FmrTrainClose :=
  fmrTrainClose_of trainComparison_proof (trainTransverseTails_of_parts hFD hMP hMD hVort hTails)

/-- Unconditional **`FmrTrainClose`** (`PartIII-a:T21/c2/2/1`, SP lines 2085-2090, 291-303, 463-467,
541-543). -/
theorem fmrTrainClose : FmrTrainClose :=
  fmrTrainClose_of_partI overlap_fluctuation_decay overlap_mean_primitive overlap_mean_decay
    train_vorticity_gaussian_tail train_stream_velocity_pressure_tails

end UnforcedLeray.Short.IIIa

