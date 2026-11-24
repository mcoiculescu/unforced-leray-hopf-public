import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_1_2.ChartPhaseAvg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_1_2.CylPolar
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_1_2.ChartJacobian

/-!
# `PartIII-b:C/rep/5/2/1/2`: `ChartPhysL2` (assembly)

Source `the November 2 reference manuscript` 2683-2689. The statement `ChartPhysL2`
is proved from the three change-of-variables lemmas `chartPhaseAvg` (step (i)), `cylPolar`
(step (ii)) and `chartJacobian` (step (iii)) by `chartPhysL2_of`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem chartPhysL2 : ChartPhysL2 :=
  chartPhysL2_of chartPhaseAvg cylPolar chartJacobian

end UnforcedLeray.Short.PartIIIb.Concrete
