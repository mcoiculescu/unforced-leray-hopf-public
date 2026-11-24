import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.GradPerSum
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth

/-! # `PartIII-a:T21/c5/1/1`: `normAmplCutFTC` (SP lines 2898-2918, 2998-3000). -/

namespace UnforcedLeray.Short.IIIa

theorem normAmplCutFTC (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.NormAmplCutFTC κ :=
  normAmplCutFTC_of κ (seedLamGradPerSum κ) (physFrameLamSmooth κ)

end UnforcedLeray.Short.IIIa
