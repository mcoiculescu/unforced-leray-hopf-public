import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1_2_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.ChartJets.AgeJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.ChartJets.PhaseJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.ChartJets.TransJets

/-!
# Chart jets, task `PartII-b:G4/5/2/1/2`

Source of record: `the November 2 reference manuscript` lines 2346-2366.
`ChartJets` (restated with the factor `1 + |Axi.trans R y|`) is assembled from the three
component bounds `ageJets`, `phaseJets`, `transJets` by `chartJets_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem chartJets : UnforcedLeray.Short.IIb.ChartJets :=
  chartJets_of ageJets phaseJets transJets

end UnforcedLeray.Short.IIb
