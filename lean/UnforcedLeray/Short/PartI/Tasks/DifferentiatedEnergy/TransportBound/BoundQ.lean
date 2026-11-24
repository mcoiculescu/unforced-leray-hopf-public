import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_3_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundB.Expand
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundQ.Top
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundQ.Ends
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundQ.Mid

/-!
# Part I, task `PartI:T08/7/3/1` (`JTBoundQ`): assembly

Source: `the November 2 reference manuscript` lines 352-358.
Assembles `JTBoundQ` from the integrated Leibniz expansion `JTExpand` (`BoundB/Expand.lean`),
the top-term vanishing `JTQTop` (`BoundQ/Top.lean`), the end terms `JTQEnds` (`BoundQ/Ends.lean`)
and the middle terms `JTQMid` (`BoundQ/Mid.lean`), via `jtBoundQ_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target** `jtBoundQ_proof` (task `PartI:T08/7/3/1`): `JTBoundQ`, assembled by `jtBoundQ_of`
from the four leaves. -/
theorem jtBoundQ_proof : UnforcedLeray.Short.PartI.JTBoundQ :=
  jtBoundQ_of jtExpand_proof jtQTop_proof jtQEnds_proof jtQMid_proof

end UnforcedLeray.Short.PartI
