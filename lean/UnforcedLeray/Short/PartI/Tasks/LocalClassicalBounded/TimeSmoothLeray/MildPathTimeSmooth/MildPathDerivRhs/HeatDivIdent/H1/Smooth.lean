import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.SmoothTensorRep
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.SmoothTensorHeatIsVecHeat
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.RowDivTensorPointwise
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.AdvDivSmoothAe

/-!
# Part I, `PartI:T02/1/4/4/1/5/1/1`: assembly of `HeatDivSmoothCase`

Source of record: `the November 2 reference manuscript`, lines 3594-3625.
Applies `heatDivSmoothCase_of` to the four sibling lemmas of folder `H1/`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

theorem heatDivSmoothCase : HeatDivSmoothCase :=
  heatDivSmoothCase_of smoothTensorRep smoothTensorHeatIsVecHeat rowDivTensorPointwise
    advDivSmoothAe

end UnforcedLeray.Short.PartI
