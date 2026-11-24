import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_3
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.PdCxPeriodic
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.IbpPdCxWeak
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.WeakCellAeUnique

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Task** `PartIII-a:T21/2/7/2/1/2/1/3/3`: `SmoothAeJet` from the three analytic leaves
`PdCxPeriodic`, `IbpPdCxWeak` and `WeakCellAeUnique` (SP lines 3060-3061). -/
theorem smoothAeJet : UnforcedLeray.Short.IIIa.SmoothAeJet :=
  smoothAeJet_of ibpPdCxWeak weakCellAeUnique pdCxPeriodic

end UnforcedLeray.Short.IIIa
