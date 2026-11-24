import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.TrainStreamYoungJets
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.RawProfileYoungJets
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.CorrYoungJets
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof

/-!
# `BgYoungW2` (`PartIII-b:C/ward/12`)

Assembly of `BgYoungW2` from the three open leaves (`BgTrainStreamYoungJets`,
`BgRawProfileYoungJets`, `BgCorrYoungJets`), with the Part I inputs `TrainFluctuationDecay`
(`PartI:T22`) and `TrainMeanExpansion` (`PartI:T23`) obtained from the unconditional Part I chain
(overlap high norm, overlap fluctuation decay, train overlap, train stream tails, vorticity tail,
mean primitive), which is re-assembled here because the packaged `_uncond` lemmas are private.
Source of record: `the November 2 reference manuscript` 1206-1222, 2347-2387,
2525-2562, 2607-2609, 5461-5464.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`BgYoungW2` is proved**: the Part I train inputs are assembled unconditionally, then
`bgTrainStreamYoungJets_of` → `bgRawProfileYoungJets_of` → `bgYoungW2_of_corr` with `bgCorrYoungJets`. -/
theorem bgYoungW2_proved : BgYoungW2 := by
  have hFD0 : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hFD0
      (UnforcedLeray.Short.PartI.overlap_mean_decay
        UnforcedLeray.Short.PartI.overlap_highnorm_uniform hFD0
        UnforcedLeray.Short.PartI.overlap_mean_primitive)
  have hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv
      (UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv)
  have hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay :=
    UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  have hM : UnforcedLeray.Short.PartI.TrainMeanExpansion :=
    UnforcedLeray.Short.PartI.trainMeanExpansion_proof hTails hFD
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  exact bgYoungW2_of_corr
    (bgRawProfileYoungJets_of (bgTrainStreamYoungJets_of hFD hM))
    bgCorrYoungJets

end UnforcedLeray.Short.PartIIIb.Concrete
