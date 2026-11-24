import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_3_1
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14.StressEpsHalfDriftDissipation.ShiftEta
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14.StressEpsHalfDriftDissipation.ShiftS

/-!


Source of record: `the November 2 reference manuscript`,
lines 1752–1756, 1769–1773, 1782–1785 (`near:local-smoothing`).

Combines the unconditional smooth-test half-drift/dissipation bounds and density extensions from
`UnforcedLeray.Short.«PartII-a».Sub.«PartII-a_N05_3_1»` with:
- `N05FlowAux.phaseHalfDriftCutoffShiftS : PhaseHalfDriftCutoffShiftS` (`ShiftS.lean`), and
- `N05FlowAux.phaseDissipationCutoffShiftEta : PhaseDissipationCutoffShiftEta` (`ShiftEta.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem stressEpsHalfDriftDissipation : UnforcedLeray.Short.PartIIa.StressEpsHalfDriftDissipation :=
  stressEpsHalfDriftDissipation_of
    N05FlowAux.phaseHalfDriftCutoffShiftS
    N05FlowAux.phaseDissipationCutoffShiftEta

end UnforcedLeray.Short.PartIIa
