import UnforcedLeray.Short.PartIIIa.Sub.T23_4_Leaves
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4.TrainVel
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4.RaisedStream
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4.RawChart
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4.AbsorbHeat
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4.AbsorbGauss
import UnforcedLeray.Short.PartIIIa.Sub.T23_4_6_Uniform
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails

/-!
# Part III-a, task `PartIII-a:T23/4`: transverse tail of the train and raw chart (`stress-short:transverse`)

Source of record: `the November 2 reference manuscript`, lines 2739-2756
(`stress-short:transverse`), 463-467 (`sct:transverse`), and 255-258 (`P_S`).

Assembles:
* `tailAbsorb : TailAbsorb` unconditionally from `tailAbsorbHeat` (`PartIII-a:T23/4/4`) and
  `tailAbsorbGauss` (`PartIII-a:T23/4/5`);
* `rawTransverseTail_of_uniform`: `RawTransverseTail` from `TrainTransverseTailsUniform`;
* `rawTransverseTail_of_partI`: `RawTransverseTail` from `PartI.TrainTransverseTails`;
* `rawTransverseTail_of_vort_tails`: `RawTransverseTail` from `PartI.TrainVorticityGaussianTail`
  (`PartI:T20`) and `PartI.TrainStreamVelocityPressureTails` (`PartI:T21`) via
  `PartI.trainTransverseTails_proof` (`PartI:T24`);
* `rawTransverseTail_of_parts`: `RawTransverseTail` from `PartI:T12..T16`, `PartI:T20`, `PartI:T21`,
  and `PartI:T24`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb UnforcedLeray.Short.PartI

/-- Unconditional absorption bound `TailAbsorb` combining `tailAbsorbHeat` and `tailAbsorbGauss`. -/
theorem tailAbsorb : UnforcedLeray.Short.IIIa.TailAbsorb :=
  tailAbsorb_of tailAbsorbHeat tailAbsorbGauss

/-- `RawTransverseTail` from `TrainTransverseTailsUniform`. -/
theorem rawTransverseTail_of_uniform (U : UnforcedLeray.Short.IIIa.TrainTransverseTailsUniform) :
    UnforcedLeray.Short.IIIa.RawTransverseTail :=
  rawTransverseTail_of (trainVelTransverseTail_of U tailAbsorb) (rawChartTail_of_uniform U tailAbsorb)

/-- `RawTransverseTail` from `PartI.TrainTransverseTails` via `trainTransverseTailsUniform_of`. -/
theorem rawTransverseTail_of_partI (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) :
    UnforcedLeray.Short.IIIa.RawTransverseTail :=
  rawTransverseTail_of_uniform (trainTransverseTailsUniform_of hT)

/-- `RawTransverseTail` from `PartI.TrainVorticityGaussianTail` (`PartI:T20`) and
`PartI.TrainStreamVelocityPressureTails` (`PartI:T21`) via `PartI.trainTransverseTails_proof`
(`PartI:T24`). -/
theorem rawTransverseTail_of_vort_tails
    (hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail)
    (hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails) :
    UnforcedLeray.Short.IIIa.RawTransverseTail :=
  rawTransverseTail_of_partI (UnforcedLeray.Short.PartI.trainTransverseTails_proof hVort hTails)

/-- `RawTransverseTail` assembled from all Part I overlap and tail tasks (`PartI:T12..T16`,
`PartI:T20`, `PartI:T21`, `PartI:T24`). -/
theorem rawTransverseTail_of_parts
    (hFD : OverlapHighNormUniform → OverlapFluctuationDecay)
    (hMP : OverlapMeanPrimitive)
    (hMD : OverlapHighNormUniform → OverlapFluctuationDecay → OverlapMeanPrimitive → OverlapMeanDecay)
    (hVort : TrainOverlap → TrainVorticityGaussianTail)
    (hTails : TrainOverlap → TrainVorticityGaussianTail → TrainStreamVelocityPressureTails) :
    UnforcedLeray.Short.IIIa.RawTransverseTail :=
  let hOv : TrainOverlap := trainOverlap_proof (hFD overlap_highnorm_uniform)
    (hMD overlap_highnorm_uniform (hFD overlap_highnorm_uniform) hMP)
  rawTransverseTail_of_vort_tails (hVort hOv) (hTails hOv (hVort hOv))

/-- Main transverse tail theorem (`stress-short:transverse`). -/
theorem rawTransverseTail : UnforcedLeray.Short.IIIa.RawTransverseTail :=
  rawTransverseTail_of_parts
    overlap_fluctuation_decay
    overlap_mean_primitive
    overlap_mean_decay
    train_vorticity_gaussian_tail
    train_stream_velocity_pressure_tails

end UnforcedLeray.Short.IIIa
