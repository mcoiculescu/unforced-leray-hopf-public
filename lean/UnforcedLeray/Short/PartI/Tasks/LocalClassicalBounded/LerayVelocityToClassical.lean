import UnforcedLeray.Short.PartI.Sub.T02_1_5
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical.ClosedParamIntegral
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical.ForceSmooth
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical.OrthCurlFree
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical.OrthMeanZero
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical.RadialPotGrad
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical.RadialPotPeriodic

/-!
# Part I, task `PartI:T02/1/5`: `LerayVelocityToClassical` (assembly)

Source of record: `the November 2 reference manuscript`, lines 261-288 (the
bounded periodic pressure choice, line 277).  This file is pure assembly: the conditional theorem
`lerayVelocityToClassical_of` (`Short/PartI/Sub/T02_1_5.lean`) applied to the six leaf theorems
`closedParamIntegralSmooth`, `lerayForceSmooth`, `orthCurlFree`, `orthMeanZero`, `radialPotGrad`,
`radialPotPeriodic`, each proved in `Tasks/LocalClassicalBounded/LerayVelocityToClassical/`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **`LerayVelocityToClassical`**: a velocity solving the Leray form of the equation admits a
smooth periodic pressure with the momentum equation for `0 < s < T`.  Assembled from the six
accepted leaves. -/
theorem lerayVelocityToClassical : LerayVelocityToClassical :=
  lerayVelocityToClassical_of closedParamIntegralSmooth lerayForceSmooth orthCurlFree
    orthMeanZero radialPotGrad radialPotPeriodic

end UnforcedLeray.Short.PartI
