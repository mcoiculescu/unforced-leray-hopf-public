import UnforcedLeray.Short.PartI.Sub.T02_1_4_4
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence

/-!
# Part I, task `PartI:T02/1/4/4`: time smoothness of the mild path (assembly, unconditional)

Source of record: `the November 2 reference manuscript`, lines 261-288.

Assembly of `MildPathTimeSmooth` (`Short/PartI/Sub/T02_1_4.lean`) from the accepted persistence
theorem `hkPersistence` (`PartI:T02/1/2`) and the derivative leaf `mildPathDerivRhs`
(`PartI:T02/1/4/4/1`), via `mildPathTimeSmooth_of` (`Short/PartI/Sub/T02_1_4_4.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

/-- **`MildPathTimeSmooth`, unconditionally** (source lines 261-288; Gallay-Slijepcevic 2015,
Theorem 1.1). Assembled as `mildPathTimeSmooth_of hkPersistence mildPathDerivRhs`. -/
theorem mildPathTimeSmooth : MildPathTimeSmooth :=
  mildPathTimeSmooth_of hkPersistence mildPathDerivRhs

end UnforcedLeray.Short.PartI
