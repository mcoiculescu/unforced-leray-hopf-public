import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1_2
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PerGramSmooth
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PhysFrameLam0Smooth

/-!
# Part III-a, task `PartIII-a:T21/c5/1/1/2`: joint smoothness of `physFrameLam` (`PhysFrameLamSmooth`)

Source of record: `the November 2 reference manuscript` (SP), lines 2520-2525 and
2891-2913. Assembled from `perGramSmooth` (`PartIII-a:T21/c5/1/1/2/1`) and
`physFrameLam0Smooth` (`PartIII-a:T21/c5/1/1/2/2`) via `physFrameLamSmooth_of`.
-/

theorem physFrameLamSmooth (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.PhysFrameLamSmooth κ :=
  UnforcedLeray.Short.IIIa.physFrameLamSmooth_of κ
    (UnforcedLeray.Short.IIIa.perGramSmooth κ)
    (UnforcedLeray.Short.IIIa.physFrameLam0Smooth κ)
