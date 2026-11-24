import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.Sub.EnvelopeOf
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof

/-!
# `convGEnvelope` (`PartIII-b:C/asrc/ra/9/2/2/13`)

Source of record: `the November 2 reference manuscript`, lines 5034-5044.
Assembles `ConvGEnvelope as χf` via `convGEnvelope_of_partI` from `trainTransverseTails_proof`
(`PartI:T24`, lines 460-467) and `trainFixedBand_proof` (`PartI:T25`, lines 468-478).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI

theorem convGEnvelope (as : ℝ) (χf : ℝ → ℝ) : ConvGEnvelope as χf := by
  have hHN : OverlapHighNormUniform := overlap_highnorm_uniform
  have hOFD : OverlapFluctuationDecay := overlap_fluctuation_decay hHN
  have hMP : OverlapMeanPrimitive := overlap_mean_primitive
  have hMD : OverlapMeanDecay := overlap_mean_decay hHN hOFD hMP
  have hOv : TrainOverlap := trainOverlap_proof hOFD hMD
  have hVort : TrainVorticityGaussianTail := train_vorticity_gaussian_tail hOv
  have hTails : TrainStreamVelocityPressureTails := train_stream_velocity_pressure_tails hOv hVort
  have hFD : TrainFluctuationDecay := trainFluctuationDecay_proof hTails hOFD hOv
  exact convGEnvelope_of_partI as χf (trainTransverseTails_proof hVort hTails)
    (trainFixedBand_proof hTails hFD)

end UnforcedLeray.Short.PartIIIb.Concrete

end
