import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Strip
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath.FluxContinuity

/-!
# Part III-a, `PartIII-a:T21/3/1`: existence of the horizon flux paths

Source of record: `the November 2 reference manuscript` lines 2819-2836 and
the finite-horizon bounds at lines 270-288 and 460-467.  The age-uniform flux path is not used;
for every age horizon `T ≥ 0` the finite-horizon train bounds and the strong continuity of the
clamped actual flux (`fluxContinuityOn`) give an `ActualTrainFluxPathOn`
(`fluxPathExistsAll_of`, `Sub/T21_3_Strip.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace UnforcedLeray.Short.IIIa.Exist

theorem fluxPathExistsAll : UnforcedLeray.Short.IIIa.Exist.FluxPathExistsAll :=
  fluxPathExistsAll_of fluxContinuityOn

end UnforcedLeray.Short.IIIa.Exist

end
