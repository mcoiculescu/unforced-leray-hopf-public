import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H2

/-!
# Part I, task `PartI:T02/1/4/4/1/5`: `HeatDivIdent` assembled from its two leaves

Target: `HeatDivIdent` (`Short/PartI/Sub/T02_1_4_4_1.lean`).  Leaves: `heatDivIdentGeneral`
(`HeatDivIdent/H1.lean`) and `weakDivZeroH5` (`HeatDivIdent/H2.lean`), combined by
`heatDivIdent_of` (`Short/PartI/Sub/PartI_T02_1_4_4_1_5.lean`).
Source of record: `the November 2 reference manuscript`, lines 261-288.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

theorem heatDivIdent : HeatDivIdent :=
  heatDivIdent_of heatDivIdentGeneral weakDivZeroH5

end UnforcedLeray.Short.PartI
