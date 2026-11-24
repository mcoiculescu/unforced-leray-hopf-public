import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.GaussCore
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound

/-!
# Part III-a, task `PartIII-a:T21/c5/3`: complement coupling bound (`AmplComplCoupling`, SP 2866-2918, 2990-2997, 3001-3004)

Decomposed via `UnforcedLeray.Short.«PartIII-a».Sub.«PartIII-a_T21_c5_3»`: once
`PartIII-a:T21/c5/3/1` (`movLamDualHeatBound` in
`UnforcedLeray.Short.«PartIII-a».Clock.FrameAmplitudeProof.ComplCoupling.HeatBound`) and
`PartIII-a:T21/c5/3/2` (`movLamDualEulerSubBound` in
`UnforcedLeray.Short.«PartIII-a».Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound`) are
proved, assemble:
```lean
theorem amplComplCoupling (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.AmplComplCoupling κ :=
  UnforcedLeray.Short.IIIa.amplComplCoupling_of κ
    (movLamDualHeatBound κ) (movLamDualEulerSubBound κ)
```
-/

namespace UnforcedLeray.Short.IIIa

/-- Conditional assembly (SP 2866-2918): `AmplComplCoupling κ` from the heat bound and the planar seed
duality `PlanarSeedEulerDual κ` (the single remaining input of `PartIII-a:T21/c5/3/2`). -/
theorem amplComplCoupling_of_dual (κ : PlanarFrameKernels)
    (hD : EulerSubCore.PlanarSeedEulerDual κ) : AmplComplCoupling κ :=
  amplComplCoupling_of κ (movLamDualHeatBound κ)
    (EulerSubCore.movLamDualEulerSubBound_of_dual κ hD)

end UnforcedLeray.Short.IIIa

theorem amplComplCoupling (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.AmplComplCoupling κ :=
  UnforcedLeray.Short.IIIa.amplComplCoupling_of κ
    (UnforcedLeray.Short.IIIa.movLamDualHeatBound κ) (movLamDualEulerSubBound κ)
