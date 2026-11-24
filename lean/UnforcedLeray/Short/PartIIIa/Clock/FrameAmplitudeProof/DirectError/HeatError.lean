import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.HeatDecomp
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.OscGramApprox

/-!
# Part III-a, task `PartIII-a:T21/c5/2/1`: heat/dilation direct error (`DirectHeatError`, SP 2893, 2905-2912, 2991-2995)

Assembly of `DirectHeatError κ` from `movLam0HeatDecomp κ` (`PartIII-a:T21/c5/2/1/1`)
and `perOscGramApprox κ` (`PartIII-a:T21/c5/2/1/2`) via `directHeatError_of`.
-/

theorem directHeatError (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.DirectHeatError κ :=
  UnforcedLeray.Short.IIIa.directHeatError_of κ
    (UnforcedLeray.Short.IIIa.movLam0HeatDecomp κ) (UnforcedLeray.Short.IIIa.perOscGramApprox κ)
