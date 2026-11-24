import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionBase
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AdvectionStep
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.LerayStep
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.RhsFamilyOf
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatDivIdent
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.MildDuhamelStrongFormOf
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.AbstractStrongDuhamel
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatStrongDuhamelOf

/-!
# Part I, task `PartI:T02/1/4/4/1`: the time derivative of the mild path in every `H^m`

Assembly of the unconditional derivative leaf `MildPathDerivRhs` (`Short/PartI/Sub/T02_1_4_4.lean`)
from the nine leaf files in `MildPathDerivRhs/`.  Source of record:
`the November 2 reference manuscript`, lines 261-288.  The proof term is
`mildPathDerivRhs_of` (`Sub/T02_1_4_4_1.lean`) applied to the nine leaves.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

/-- **`MildPathDerivRhs`, unconditionally** (source lines 261-288; Gallay-Slijepcevic 2015,
Theorem 1.1: the mild solution is smooth for positive time, the datum is smooth, solenoidal and in
every `H^k`).  Assembled from the leaves `advectionBase`, `advectionStep`, `lerayStep`,
`heatDivIdent`, `heatGeneratorH5`, `abstractStrongDuhamel`, via `rhsFamily_of`,
`mildDuhamelStrongForm_of`, `heatStrongDuhamel_of`, `advectionBilinear_of`, `lerayLevels_of`. -/
theorem mildPathDerivRhs : MildPathDerivRhs :=
  mildPathDerivRhs_of
    (rhsFamily_of (advectionBilinear_of advectionBase advectionStep) (lerayLevels_of lerayStep))
    (mildDuhamelStrongForm_of heatDivIdent)
    (heatStrongDuhamel_of heatGeneratorH5 abstractStrongDuhamel)

end UnforcedLeray.Short.PartI
