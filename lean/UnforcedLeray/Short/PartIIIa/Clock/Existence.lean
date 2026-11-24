import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Horizon
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak
import UnforcedLeray.Short.PartIIIa.Clock.Existence.ScaleSupplier
import UnforcedLeray.Short.PartIIIa.Clock.Existence.BiotSavartField
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxIdentity
import UnforcedLeray.Short.PartIIIa.Clock.Existence.MildIntegrated
import UnforcedLeray.Short.PartIIIa.Clock.Existence.StripContinuity
import UnforcedLeray.Short.PartIIIa.Clock.Existence.StripBookkeeping
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FlowAppend
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FlowCongrAE
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FlowGlobal

/-!
# Part III-a, `PartIII-a:T21/3`: `FullFlowExistsSmall` from its leaves

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
The conditional assembly `fullFlowExistsSmall_of` (`Sub/T21_3_Horizon.lean`) is applied to the
accepted leaf theorems of the `Clock/Existence` folder.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace UnforcedLeray.Short.IIIa.Exist

/-- `PartIII-a:T21/3`: existence of the full evolution in the range `0 < ν ≤ 1`, for every train
with finite-horizon coefficient bounds. -/
theorem fullFlowExistsSmall : UnforcedLeray.Short.IIIa.Exist.FullFlowExistsSmall :=
  fullFlowExistsSmall_of fluxPathExistsAll unitHeatWeakActual scaleSupplier biotSavartFieldAll
    fluxIdentityOnAll mildIntegratedOnAll stripContinuityOnAll stripBookkeepingOn flowAppend
    flowCongrAE flowGlobal

end UnforcedLeray.Short.IIIa.Exist

end
