import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.Smooth
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent.H1.Reps

/-!
# Part I, `PartI:T02/1/4/4/1/5/1`: assembly of `HeatDivIdentGeneral`

Source of record: `the November 2 reference manuscript`, lines 3594-3625 and 261-288.
Applies `heatDivIdentGeneral_of` to `heatDivSmoothCase` (file `H1/Smooth.lean`) and
`advDivContinuousReps` (file `H1/Reps.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

theorem heatDivIdentGeneral : HeatDivIdentGeneral :=
  heatDivIdentGeneral_of heatDivSmoothCase advDivContinuousReps

end UnforcedLeray.Short.PartI
