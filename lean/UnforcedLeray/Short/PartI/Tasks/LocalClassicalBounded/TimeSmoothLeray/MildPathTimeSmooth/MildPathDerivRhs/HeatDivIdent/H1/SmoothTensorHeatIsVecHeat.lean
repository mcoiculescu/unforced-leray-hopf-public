import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1_2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.SmoothTensorHeatIsVecHeat.smoothRowDivHeatPointwise
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.SmoothTensorHeatIsVecHeat.rowDivPeriodicMemLp
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.SmoothTensorHeatIsVecHeat.heatDivH3NormalizedAe
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.SmoothTensorHeatIsVecHeat.normalizedValueOfAe
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.SmoothTensorHeatIsVecHeat.heatVecL2Periodic

/-!
# `smoothTensorHeatIsVecHeat`: smooth tensors, heat divergence is the vector heat

Source of record: `the November 2 reference manuscript`, lines 3594-3625.
Assembles the five facts of `PartI_T02_1_4_4_1_5_1_1_2.lean` (`smoothTensorHeatIsVecHeat_of`)
with their proofs in the sibling files of folder `SmoothTensorHeatIsVecHeat/`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

theorem smoothTensorHeatIsVecHeat : SmoothTensorHeatIsVecHeat :=
  smoothTensorHeatIsVecHeat_of smoothRowDivHeatPointwise rowDivPeriodicMemLp
    heatDivH3NormalizedAe normalizedValueOfAe heatVecL2Periodic

end UnforcedLeray.Short.PartI
