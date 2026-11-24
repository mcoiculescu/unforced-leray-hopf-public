import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreCoeff
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.HomogeneousZero

/-!
# Part III-a, task `PartIII-a:T19`: the polynomial causal inverse (`prop:short-polynomial-causal`)

Source of record: `the November 2 reference manuscript` (SP), lines 3426-3546.
Target (`FlatCausal.lean`):
`theorem polyCausal (hClock : FullClockWeakForward) (hFree : FreeCausalExistsUnique) (hHardy : HardyKernel) : PolyCausal`.

The conditional assembly `polyCausal_of` and the four leaf statements
`TrainCoreCoeffBound` (`PartIII-a:T19/1`), `CoreDuhamelBiotSavart` (`PartIII-a:T19/2`),
`TailEnergyContinuation` (`PartIII-a:T19/3`), and `TrainCausalHomogeneousZero` (`PartIII-a:T19/4`)
are defined and proved in `Short/PartIII-a/Sub/PartIII-a_T19.lean`.
-/

namespace UnforcedLeray.Short.IIIa

theorem polyCausal (hClock : FullClockWeakForward) (hFree : FreeCausalExistsUnique)
    (hHardy : HardyKernel) : PolyCausal :=
  polyCausal_of hClock hFree hHardy trainCoreCoeffBound coreDuhamelBiotSavart
    tailEnergyContinuation trainCausalHomogeneousZero

end UnforcedLeray.Short.IIIa
