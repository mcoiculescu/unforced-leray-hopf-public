import UnforcedLeray.Short.PartIIb.Sub.T22_1_6
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatMoments
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatGrad.KdDominated
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatGrad.KHasFDeriv

/-!


Proves `HeatGradFormula` (`Sub/T22_1/Stages.lean`) by `heatGradFormula_of`, applied to
`HeatKernelMoments` (task `T22/1/3`, `HeatMoments.lean`), `HeatKdDominated` (leaf `T22/1/6/1`)
and `HeatKHasFDeriv` (leaf `T22/1/6/2`). Source `the November 2 reference manuscript`,
lines 2074-2093, 2103-2105.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

/-- **`PartII-b:T22/1/6`** Differentiation under the integral sign for `e^{aΔ} g`. -/
theorem heatGradFormula : UnforcedLeray.Short.IIb.CylPDE.HeatGradFormula :=
  heatGradFormula_of heatKernelMoments heatKdDominated heatKHasFDeriv

end UnforcedLeray.Short.IIb.CylPDE
