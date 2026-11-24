import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound.SharpDecay
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1_1.SeedJet

/-!
# Part III-a, task `PartIII-a:T21/c5/3/1/1`: unconditional `SeedLamPDSharpDecay`

Source of record: `the November 2 reference manuscript` (SP), lines 2896-2912.

This file closes the conditional assembly `seedLamPDSharpDecay_of` (in `SharpDecay.lean`) by
feeding it the unconditional leaf `seedLamPJet2Decay_all` (in `SeedJet.lean`).

`SharpDecay.lean` cannot import `SeedJet.lean` directly: `SeedJet.lean` imports
`Sub.PartIII-a_T21_c5_3_1_1`, which imports `SharpDecay.lean`. So the theorem lives in this
separate file, which imports both.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- `SeedLamPDSharpDecay κ` holds for every planar frame kernel `κ`
(`PartIII-a:T21/c5/3/1/1`, SP lines 2896-2912). -/
theorem seedLamPDSharpDecay (kappa : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.SeedLamPDSharpDecay kappa :=
  seedLamPDSharpDecay_of kappa (seedLamPJet2Decay_all kappa)

end UnforcedLeray.Short.IIIa
