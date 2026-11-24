import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.DualUnfold
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.DualFubini
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.DualRep

/-!
# Part III-a, `PartIII-a:T21/3/2/2/2`: the dual heat pairing `UnitHeatDual`

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Proves `UnitHeatDual cylHeatSmooth` (N2) from the three pieces `UnitHeatDualUnfold`,
`HeatDivFluxDual`, `FluxPairPeriodicRep` via `unitHeatDual_of` (`DualSplit.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

theorem unitHeatDual : UnforcedLeray.Short.IIIa.Exist.UnitHeatDual UnforcedLeray.Short.IIIa.Exist.cylHeatSmooth :=
  unitHeatDual_of unitHeatDualUnfold heatDivFluxDual fluxPairPeriodicRep

end UnforcedLeray.Short.IIIa.Exist
