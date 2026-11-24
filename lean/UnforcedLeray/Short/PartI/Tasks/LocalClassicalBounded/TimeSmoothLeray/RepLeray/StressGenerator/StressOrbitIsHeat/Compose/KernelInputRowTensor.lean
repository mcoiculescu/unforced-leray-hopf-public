import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_1_1_6_Bridges
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Compose.KernelInputPeriodicAE
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Compose.VecH3ZeroClassValueAE

/-!
# Sub2: `KernelInputRowTensor`

Proves `KernelInputRowTensor` (Sub file, Sub2; source lines 261-288 of
`the November 2 reference manuscript`) from `kernelInputRowTensor_of`
(Bridges file) applied to the leaf theorems `tensorKernelInputPeriodicAE` (Bridge 2a) and
`vecH3ZeroClassValueAE` (Bridge 2b).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem kernelInputRowTensor : KernelInputRowTensor :=
  kernelInputRowTensor_of tensorKernelInputPeriodicAE vecH3ZeroClassValueAE

end UnforcedLeray.Short.PartI
