import UnforcedLeray.Short.PartIIb.Sub.T12_7_7_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Slice.Support
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.DuhamelIntegrable.BoxSlice

/-!
# Helper for `PartII-b:T12/7/7/2` (`deqAbsSlice`): the conditional reduction, unconditioned

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

`deqAbsSlice_of` reduces `DeqAbsSlice` to `BoxSlice` (leaf `PartII-b:T12/6/2/5`, proved in
`DuhamelSolenoidal/DuhamelIntegrable/BoxSlice.lean`) and `DeqAbsSupport` (leaf `PartII-b:T12/7/7/2/1`,
proved in `Slice/Support.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/7/2`**: `DeqAbsSlice`, from the box slice bound and the transpose-test
support bound. -/
theorem deqAbsSlice : UnforcedLeray.Short.IIb.DeqAbsSlice :=
  deqAbsSlice_of boxSlice deqAbsSupport

end UnforcedLeray.Short.IIb
