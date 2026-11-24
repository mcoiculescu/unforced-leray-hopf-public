import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2_2
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.Pullback
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.SubBound

/-!
# Part III-a, task `PartIII-a:T21/c5/2/2`: linearised Euler direct error (`DirectEulerSubBound`, SP 2866-2889, 2905-2918, 2991-2995)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2889,
2905-2918, and 2991-2995 (`eq:short-causal-ampl-moving`).

Assembles `DirectEulerSubBound κ` from the children `movLam0EulerPullback`
(`PartIII-a:T21/c5/2/2/1`, file `EulerSubBound/Pullback.lean`) and `movLam0EulerSubBound`
(`PartIII-a:T21/c5/2/2/2`, file `EulerSubBound/SubBound.lean`) via `directEulerSubBound_of`.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **`DirectEulerSubBound κ` (`PartIII-a:T21/c5/2/2`)**, unconditional: composes the
children `movLam0EulerPullback κ` and `movLam0EulerSubBound κ`. -/
theorem directEulerSubBound (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.DirectEulerSubBound κ :=
  UnforcedLeray.Short.IIIa.directEulerSubBound_of κ (movLam0EulerPullback κ) (movLam0EulerSubBound κ)

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.directEulerSubBound
