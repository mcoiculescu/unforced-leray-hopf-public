import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_2_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionStep.N1.PerExtBack
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionStep.N1.PlaneProduct

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Needed N1 (analytic core).** The weak product rule for scalar times vector on the cylinder,
assembled from the periodic-extension and plane product helpers (source lines 261-288). -/
theorem cylWeakProductSmul : CylWeakProductSmul :=
  cylWeakProductSmul_of perExtCylBack planeProductSmul

end UnforcedLeray.Short.PartI
