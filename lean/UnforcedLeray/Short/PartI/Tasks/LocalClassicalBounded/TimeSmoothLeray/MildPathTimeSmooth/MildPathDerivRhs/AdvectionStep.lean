import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionStep.N2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionStep.N4
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionStep.N5

/-!
# Part I, task `PartI:T02/1/4/4/1/2`: the advection step `m → m + 1`

Source of record: `the November 2 reference manuscript`, lines 261-288.

Assembly: `advectionStep_of` (`Sub/PartI_T02_1_4_4_1_2.lean`) applied to
`cylGlueFirstOrder` (N2), `cylSobNormSucc` (N4) and `advectionWeakLeibniz` (N5).
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

/-- The advection step: `AdvectionAt c m → AdvectionAt c (m + 1)` for `m ≥ 3`. -/
theorem advectionStep : AdvectionStep :=
  advectionStep_of cylGlueFirstOrder cylSobNormSucc advectionWeakLeibniz

end UnforcedLeray.Short.PartI
