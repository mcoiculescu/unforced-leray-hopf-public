import UnforcedLeray.Short.PartIIIa.Sub.T21_3
import UnforcedLeray.Short.PartIIIa.Clock.Existence
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath.TrainBoundsSmall
import UnforcedLeray.Short.PartIIIa.Clock.LongFull
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4
import UnforcedLeray.Short.PartIIIa.Clock.WeakFromLong
import UnforcedLeray.Short.PartIIIa.Clock.ShortWeakSmoothing
import UnforcedLeray.Short.PartIIIa.Clock.ZeroCirc
import UnforcedLeray.Short.PartIIIa.T06_ScalingJa
import UnforcedLeray.Short.PartIIIa.T07_ScalingJaInv
import UnforcedLeray.Short.PartIIIa.T08_ScalingJaInvDual

/-!
# Part III-a, task `PartIII-a:T21`: full-clock long and weak forward estimates

Source: `the November 2 reference manuscript`.
Assembles `fullClockLongForward` and `fullClockWeakForward`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

private theorem u_uncond : TrainTransverseTailsUniform :=
  let hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof
      (UnforcedLeray.Short.PartI.overlap_fluctuation_decay
        UnforcedLeray.Short.PartI.overlap_highnorm_uniform)
      (UnforcedLeray.Short.PartI.overlap_mean_decay
        UnforcedLeray.Short.PartI.overlap_highnorm_uniform
        (UnforcedLeray.Short.PartI.overlap_fluctuation_decay
          UnforcedLeray.Short.PartI.overlap_highnorm_uniform)
        UnforcedLeray.Short.PartI.overlap_mean_primitive)
  let hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail :=
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  let hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  trainTransverseTailsUniform_of
    (UnforcedLeray.Short.PartI.trainTransverseTails_proof hVort hTails)

theorem fullClockLongForward : UnforcedLeray.Short.IIIa.FullClockLongForward :=
  Exist.fullClockLongForward_of_small
    Exist.fullFlowExistsSmall
    (Exist.trainBoundsSmall_of u_uncond)
    longForwardEstimate

theorem fullClockWeakForward : UnforcedLeray.Short.IIIa.FullClockWeakForward :=
  fullClockWeakForward_of
    fullClockLongForward
    shortWeakSmoothing
    zeroCirculationPreserved
    (scalingBounds_of_parts scalingJa scalingJaInv scalingJaInvDual)

end UnforcedLeray.Short.IIIa
