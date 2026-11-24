import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_3
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14.StressEpsHalfDriftDissipation
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14.StressEpsCommutingFlowShiftQ

/-!


Source of record: `the November 2 reference manuscript`, lines 1752-1756,
1765-1788 (`near:local-smoothing`, `ε > 0` stress case).

Assembles `stressEpsLocalH14` from `stressEpsLocalH14_of`,
`stressEpsHalfDriftDissipation`, and `stressEpsCommutingFlowShiftQ`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem stressEpsLocalH14 : UnforcedLeray.Short.PartIIa.StressEpsLocalH14 :=
  stressEpsLocalH14_of stressEpsHalfDriftDissipation stressEpsCommutingFlowShiftQ

end UnforcedLeray.Short.PartIIa
