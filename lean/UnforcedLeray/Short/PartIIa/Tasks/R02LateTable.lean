import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartIIa.Tasks.R02.ProfileSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanCoeff
import UnforcedLeray.Short.PartIIa.Tasks.R02.HeatProfile
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress
import UnforcedLeray.Short.PartIIa.Tasks.R02.Commutators
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockA1
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB1
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB2
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockA2
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Part II-a, task `PartII-a:R02`: the late residual table (unconditional assembly)

Source of record: `the November 2 reference manuscript`, lines 1259-1276 (late
residual table) with Lemma `sct:heat` (lines 437-481: `sct:fluctuation` 439-446, `sct:expansion`
447-459) and the mean equations `sct:mean` (lines 397-404).

Assembles `ringLateTable : RingLateTable` from `ringLateTable_of` (`Sub/R02.lean`), the leaf
blocks `ringLateA1_of`, `ringLateB1_of`, `ringLateB2_of`, `ringLateB3_of`, `ringLateA2_of`, the
ingredient bundle `LateIngredients`, and the Part I train estimates (`TrainFluctuationDecay`,
`TrainMeanExpansion`, `TrainMeanEquations`, `TrainStreamSmooth`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R02`: the late residual table** (source lines 1259-1276). -/
theorem ringLateTable : RingLateTable := by
  have hOFluct : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOMean : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform hOFluct
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hOFluct hOMean
  have hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail :=
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay :=
    UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hOFluct hOv
  have hME : UnforcedLeray.Short.PartI.TrainMeanExpansion :=
    UnforcedLeray.Short.PartI.trainMeanExpansion_proof hTails hFD
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hS : LateProfileSmooth :=
    lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  have ing : LateIngredients :=
    ⟨hS,
     lateFluctuationProfile_of hFD hS,
     lateMeanRemainder_of hME UnforcedLeray.Short.PartI.trainMeanEquations_proof hS,
     lateMeanCoeff_of hFD UnforcedLeray.Short.PartI.trainMeanEquations_proof,
     lateHeatProfile,
     lateMeanStress_of hFD UnforcedLeray.Short.PartI.trainMeanEquations_proof hS,
     profileCommutators⟩
  exact ringLateTable_of (ringLateA1_of ing) (ringLateB1_of ing) (ringLateB2_of ing)
    (ringLateB3_of ing) (ringLateA2_of ing UnforcedLeray.Short.PartI.trainMeanEquations_proof)

end UnforcedLeray.Short.PartIIa
