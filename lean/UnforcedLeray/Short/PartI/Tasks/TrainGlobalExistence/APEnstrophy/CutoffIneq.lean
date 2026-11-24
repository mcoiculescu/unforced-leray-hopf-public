import UnforcedLeray.Short.PartI.Sub.PartI_T04_6_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.Integrable
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.Continuous
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.RhsEstimate

/-!
# `PartI:T04/6/1`: `APEnstrophyCutoffIneq` (source lines 285-287)

Assembles the four leaves (integrability, continuity, derivative identity, strip estimate)
through `apEnstrophyCutoffIneq_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- `APEnstrophyCutoffIneq` from the four leaves (source lines 285-287). -/
theorem apEnstrophyCutoffIneq : APEnstrophyCutoffIneq :=
  apEnstrophyCutoffIneq_of apEnstrophyIntegrable apEnstrophyContinuous
    apEnstrophyHasDeriv apEnstrophyRhsEstimate

end UnforcedLeray.Short.PartI
