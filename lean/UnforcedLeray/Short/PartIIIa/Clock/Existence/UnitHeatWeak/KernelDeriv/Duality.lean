import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1_2_1
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.Duality.MassTransport
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.Duality.KernelIntegrable
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.Duality.HeatLiftFst
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.LapTestBounded

/-!
# Part III-a, `PartIII-a:T21/3/2/1/2/1`: `UnitHeatDuality` (lemma A)

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Assembles the three lemmas (mass transport, duality kernel integrability, heat lift first
component) and the cylinder-test Laplacian bound into `unitHeatDuality_of`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace UnforcedLeray.Short.IIIa.Exist

theorem unitHeatDuality : UnforcedLeray.Short.IIIa.Exist.UnitHeatDuality :=
  unitHeatDuality_of massTransport dualityKernelIntegrable heatLiftFst lapTestBounded

end UnforcedLeray.Short.IIIa.Exist
