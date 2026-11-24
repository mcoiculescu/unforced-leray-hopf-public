import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC

/-!
# Part III-a, task `PartIII-a:T21/c5/1`: weak FTC for the normalised frame amplitudes (`AmplWeakFTC`, SP 2898-2918, 2991-3000)

Decomposed via `UnforcedLeray.Short.«PartIII-a».Sub.«PartIII-a_T21_c5_1»`: once
`PartIII-a:T21/c5/3/1` (`movLamDualHeatBound` in
`UnforcedLeray.Short.«PartIII-a».Clock.FrameAmplitudeProof.ComplCoupling.HeatBound`),
`PartIII-a:T21/c5/3/2` (`movLamDualEulerSubBound` in
`UnforcedLeray.Short.«PartIII-a».Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound`), and
`PartIII-a:T21/c5/1/1` (`normAmplCutFTC` in
`UnforcedLeray.Short.«PartIII-a».Clock.FrameAmplitudeProof.WeakFTC.CutFTC`) are proved, assemble:
```lean
theorem amplWeakFTC (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.AmplWeakFTC κ :=
  UnforcedLeray.Short.IIIa.amplWeakFTC_of κ
    (movLamDualHeatBound κ) (movLamDualEulerSubBound κ) (normAmplCutFTC κ)
```
-/

theorem amplWeakFTC (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.AmplWeakFTC κ :=
  UnforcedLeray.Short.IIIa.amplWeakFTC_of κ
    (UnforcedLeray.Short.IIIa.movLamDualHeatBound κ)
    (movLamDualEulerSubBound κ)
    (UnforcedLeray.Short.IIIa.normAmplCutFTC κ)
