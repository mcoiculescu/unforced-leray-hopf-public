import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.G
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.T

/-!
# `Sub/PartII-a_N05_1_1/Final`: Assembly of `PhaseD2CutoffSQE` (`PartII-a:N05/1/1`)

Source: `the November 2 reference manuscript`,
lines 1789–1793 (`near:local-smoothing`).

Combines `phaseD2CutoffSQE_of_gen` (`Sub/PartII-a_N05_1_1/G`, proved from `phaseGradTransportWt` and
`N05_1_1G.phaseCutoffProductRuleWt`) with `phaseGeneratorTransport` (`Sub/PartII-a_N05_1_1/T`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem phaseD2CutoffSQE : PhaseD2CutoffSQE :=
  phaseD2CutoffSQE_of_gen phaseGeneratorTransport

end UnforcedLeray.Short.PartIIa
