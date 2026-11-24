import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling

/-!
# Part III-a, task `PartIII-a:T21/c5`: amplitude ODE bound for the periodized frame (`FrameAmplitudeAll`)

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2933 and
2991-3000 (`eq:short-causal-moving-eq`, `eq:short-causal-damped-complement`,
`eq:short-causal-ampl-moving`).
Target (`Clock/Frame.lean`):
`theorem frameAmplitudeAll (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (h : UnforcedLeray.Short.IIIa.IsSeedKernels κ) : UnforcedLeray.Short.IIIa.FrameAmplitudeAll κ`.

The conditional assembly `frameAmplitudeAll_of`, the helper namespace `FrameAmplSub`, and the three
leaf statements `AmplWeakFTC` (`PartIII-a:T21/c5/1`), `AmplDirectError` (`PartIII-a:T21/c5/2`),
and `AmplComplCoupling` (`PartIII-a:T21/c5/3`) are defined and proved in
`Short/PartIII-a/Sub/PartIII-a_T21_c5.lean`.
-/

theorem frameAmplitudeAll (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (h : UnforcedLeray.Short.IIIa.IsSeedKernels κ) : UnforcedLeray.Short.IIIa.FrameAmplitudeAll κ :=
  UnforcedLeray.Short.IIIa.frameAmplitudeAll_of κ h (amplWeakFTC κ) (amplDirectError κ) (amplComplCoupling κ)
