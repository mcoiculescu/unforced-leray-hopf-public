import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1_2
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.Duality
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.LiftIntegrable
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.RealHeatDeriv
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.RealHeatBound
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.LapTestBounded

/-!
# Part III-a, `PartIII-a:T21/3/2/1/2`: unconditional `UnitHeatKernelDeriv`

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Assembles the five proved lemmas (duality, lift integrability, real heat derivative,
real heat bound, Laplacian of a cylinder test) into `unitHeatKernelDeriv_of`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace UnforcedLeray.Short.IIIa.Exist

theorem unitHeatKernelDeriv : UnforcedLeray.Short.IIIa.Exist.UnitHeatKernelDeriv :=
  unitHeatKernelDeriv_of unitHeatDuality unitHeatLiftIntegrable realHeatDeriv realHeatBound
    lapTestBounded

end UnforcedLeray.Short.IIIa.Exist
