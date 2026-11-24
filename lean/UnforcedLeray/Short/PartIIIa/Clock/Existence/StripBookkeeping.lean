import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Horizon
import UnforcedLeray.Short.PartIIIa.Clock.Existence.StripBookkeeping.LinFlowComb
import UnforcedLeray.Short.PartIIIa.Clock.Existence.StripBookkeeping.ActualRepresentation
import UnforcedLeray.Short.PartIIIa.Clock.Existence.StripBookkeeping.GoodCStable
import UnforcedLeray.Short.PartIIIa.Clock.Existence.StripBookkeeping.VortFnInj
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FlowCongrAE
import UnforcedLeray.Short.PartIIIa.Clock.Existence.HorizonLocality

/-!
# Part III-a, `PartIII-a:T21/3/9`: bookkeeping on horizons (assembly)

Source of record: `the November 2 reference manuscript`, the strip bookkeeping
(T21/3/9). The conditional theorem `stripBookkeepingOn_of` (in `Sub/T21_3_Horizon.lean`) is
applied to the accepted inputs `linFlowComb`, `actualRepresentation`, `goodCStable`, `vortFnInj`,
`flowCongrAE` and `horizonLocality`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace UnforcedLeray.Short.IIIa.Exist

/-- `T21/3/9` (horizon form) holds for all parameters. -/
theorem stripBookkeepingOn : UnforcedLeray.Short.IIIa.Exist.StripBookkeepingOn :=
  stripBookkeepingOn_of linFlowComb actualRepresentation goodCStable vortFnInj flowCongrAE
    horizonLocality

end UnforcedLeray.Short.IIIa.Exist
