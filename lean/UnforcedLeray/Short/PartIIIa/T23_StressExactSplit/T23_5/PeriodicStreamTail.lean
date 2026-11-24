import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.HarmonicPeriodic
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.GaussianPeriodic
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.GreenRemainder

/-!
# Part III-a, `PartIII-a:T23/5/1`: `PeriodicStreamTail` from its three leaves (SP 2349-2358)

Assembles `periodicStreamTail_of` (Sub/PartIII-a_T23_5_1.lean) with the leaves
`harmonicPeriodicDecay`, `gaussianPeriodicDecay`, `greenRemainder`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **Periodized stream tail** (SP 2349-2358), assembled from the three leaves. -/
theorem periodicStreamTail : UnforcedLeray.Short.IIIa.PeriodicStreamTail :=
  periodicStreamTail_of harmonicPeriodicDecay gaussianPeriodicDecay greenRemainder

end UnforcedLeray.Short.IIIa
