import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound

/-!
# Part III-a, task `PartIII-a:T21/c5/2`: direct frame error bound (`AmplDirectError`, SP 2866-2918, 2991-2995)

Decomposed via `UnforcedLeray.Short.«PartIII-a».Sub.«PartIII-a_T21_c5_2»`: once
`PartIII-a:T21/c5/2/1` (`directHeatError` in
`UnforcedLeray.Short.«PartIII-a».Clock.FrameAmplitudeProof.DirectError.HeatError`) and
`PartIII-a:T21/c5/2/2` (`directEulerSubBound` in
`UnforcedLeray.Short.«PartIII-a».Clock.FrameAmplitudeProof.DirectError.EulerSubBound`) are
proved, assemble:
-/

theorem amplDirectError (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.AmplDirectError κ :=
  UnforcedLeray.Short.IIIa.amplDirectError_of κ
    (directHeatError κ) (UnforcedLeray.Short.IIIa.directEulerSubBound κ)
