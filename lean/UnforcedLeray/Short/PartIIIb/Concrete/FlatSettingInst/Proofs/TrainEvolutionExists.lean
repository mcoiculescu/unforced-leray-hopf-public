import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Reduced
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Proofs.ReflHeatSupplier
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath.TrainBoundsSmall
import UnforcedLeray.Short.PartIIIa.Sub.T23_4_6_Uniform
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxIdentity
import UnforcedLeray.Short.PartIIIa.Clock.Existence.MildIntegrated
import UnforcedLeray.Short.PartIIIa.Clock.Existence.StripContinuity
import UnforcedLeray.Short.PartIIIa.Clock.Existence.HorizonLocality

/-!


Source of record: `the November 2 reference manuscript` (73 pages), lines
2819-2836 (full evolution `U(s, t)` by Volterra iteration around the actual train), 4349-4352
(`X_{m,c}` the centrally even zero-circulation subspace, `𝒰` the actual train evolution),
287-288 (the train is odd), 2934-2935 and 3100-3101 (zero circulation preserved).

Assembles `TrainEvolutionExists` via `Evol.trainEvolutionExists_of'` from:
* `trainBoundsSmall_of (trainTransverseTailsUniform_of hT)` from `PartI.TrainTransverseTails`
  (and from `PartI.TrainVorticityGaussianTail` and `PartI.TrainStreamVelocityPressureTails` via
  `PartI.trainTransverseTails_proof`);
* `fluxPathExistsAll` (`PartIII-a:T21/3/1`);

  and `PartIII-a:T21/3/2`);
* `fluxIdentityOnAll` (`PartIII-a:T21/3/5`);
* `mildIntegratedOnAll` (`PartIII-a:T21/3/6`);
* `stripContinuityOnAll` (`PartIII-a:T21/3/7`);
* `horizonLocality` (`PartIII-a:T21/3/9/5`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa.Exist

/-- **`TrainEvolutionExists`** from `PartI.TrainTransverseTails` and the unconditional Volterra
evolution existence chain. -/
theorem trainEvolutionExists_of_tails
    (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.TrainEvolutionExists :=
  Evol.trainEvolutionExists_of'
    (trainBoundsSmall_of (UnforcedLeray.Short.IIIa.trainTransverseTailsUniform_of hT))
    fluxPathExistsAll
    (Evol.reflHeatSupplierExists_of unitHeatWeakActual)
    fluxIdentityOnAll
    mildIntegratedOnAll
    stripContinuityOnAll
    horizonLocality

/-- **`TrainEvolutionExists`** from `PartI.TrainVorticityGaussianTail` (`PartI:T20`) and
`PartI.TrainStreamVelocityPressureTails` (`PartI:T21`) via `PartI.trainTransverseTails_proof`
(`PartI:T24`). -/
theorem trainEvolutionExists_of_vort_tails
    (hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail)
    (hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails) :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.TrainEvolutionExists :=
  trainEvolutionExists_of_tails
    (UnforcedLeray.Short.PartI.trainTransverseTails_proof hVort hTails)

/-- **`TrainEvolutionExists`** assembled from the accepted `PartI:T12` (`overlap_highnorm_uniform`),
`PartI:T16` (`trainOverlap_proof`), `PartI:T24` (`trainTransverseTails_proof`), and the conditional
Part I overlap and tail tasks `PartI:T13`, `PartI:T14`, `PartI:T15`, `PartI:T20`, `PartI:T21`. -/
theorem trainEvolutionExists_of_partI
    (hFD : UnforcedLeray.Short.PartI.OverlapHighNormUniform →
      UnforcedLeray.Short.PartI.OverlapFluctuationDecay)
    (hMP : UnforcedLeray.Short.PartI.OverlapMeanPrimitive)
    (hMD : UnforcedLeray.Short.PartI.OverlapHighNormUniform →
      UnforcedLeray.Short.PartI.OverlapFluctuationDecay →
      UnforcedLeray.Short.PartI.OverlapMeanPrimitive →
      UnforcedLeray.Short.PartI.OverlapMeanDecay)
    (hVort : UnforcedLeray.Short.PartI.TrainOverlap →
      UnforcedLeray.Short.PartI.TrainVorticityGaussianTail)
    (hTails : UnforcedLeray.Short.PartI.TrainOverlap →
      UnforcedLeray.Short.PartI.TrainVorticityGaussianTail →
      UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails) :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.TrainEvolutionExists :=
  let hHN := UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  let hOv := UnforcedLeray.Short.PartI.trainOverlap_proof (hFD hHN) (hMD hHN (hFD hHN) hMP)
  trainEvolutionExists_of_vort_tails (hVort hOv) (hTails hOv (hVort hOv))

/-- **`TrainEvolutionExists`**: existence of the actual planar train evolution `U(s, t)` on the
centrally even zero-circulation weighted vorticity space `X_{m,c}`. -/
theorem trainEvolutionExists :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.TrainEvolutionExists :=
  trainEvolutionExists_of_partI
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay
    UnforcedLeray.Short.PartI.overlap_mean_primitive
    UnforcedLeray.Short.PartI.overlap_mean_decay
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
