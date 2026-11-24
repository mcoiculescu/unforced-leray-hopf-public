import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Reduction
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Meas
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Slice
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Time

/-!
# Part II-b, task `PartII-b:T12/7/7` (`deqAbsIntegrable`): joint absolute integrability

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

Assembly of the three leaves `deqAbsMeas`, `deqAbsSlice` and `deqAbsTime` through the conditional
reduction `deqAbsIntegrable_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/7`**: `DeqAbsIntegrable`, from the measurability, slice and time leaves. -/
theorem deqAbsIntegrable : UnforcedLeray.Short.IIb.DeqAbsIntegrable :=
  deqAbsIntegrable_of deqAbsMeas deqAbsSlice deqAbsTime

end UnforcedLeray.Short.IIb
