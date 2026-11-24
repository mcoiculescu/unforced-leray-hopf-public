import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLBuildPieces.AvgRep
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLBuildPieces.ProfPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLBuildPieces.ProfFns
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLBuildPieces.ChartNv
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLBuildPieces.ChartMeas
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLBuildPieces.ChartPeriodic

/-!
# Part II-b, task `PartII-b:T10/7/1/1/3` (`GLBuild`): assembly

Source of record: `the November 2 reference manuscript` 1639-1668, 1912-1921.

Target: `gl_build : UnforcedLeray.Short.IIb.GLBuild`, obtained from `gl_build_of` applied to the
four pieces `GLProfFns` (via `glProfFns_of_AB`), `GLChartNv`, `GLChartMeas`, `GLChartPeriodic`.
-/

set_option autoImplicit false

noncomputable section

theorem gl_build : UnforcedLeray.Short.IIb.GLBuild :=
  UnforcedLeray.Short.IIb.gl_build_of
    (glProfFns_of_AB gl_avgRep gl_profPeriodic)
    UnforcedLeray.Short.IIb.gl_chartNv
    UnforcedLeray.Short.IIb.gl_chartMeas
    UnforcedLeray.Short.IIb.gl_chartPeriodic

#print axioms gl_build
