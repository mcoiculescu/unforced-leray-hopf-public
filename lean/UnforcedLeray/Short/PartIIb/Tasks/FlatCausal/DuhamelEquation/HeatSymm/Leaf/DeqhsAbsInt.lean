import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm.Leaf.AbsInt.DeqhsAbsMeas
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm.Leaf.AbsInt.DeqhsAbsLint

/-!
# Part II-b, task `PartII-b:T12/7/3/1` (`deqhsAbsInt`): assembly of the two leaves

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
The absolute integrability statement `DeqhsAbsInt` follows from the a.e. measurability leaf
`DeqhsAbsMeas` (`/1`) and the finiteness-of-lintegral leaf `DeqhsAbsLint` (`/5`) via
`deqhsAbsInt_of` (proved in `Sub/PartIIb_T12_7_3_1.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/3/1`** (SP 1923-1927): absolute integrability of the Fubini integrand,
assembled from the leaves `DeqhsAbsMeas` and `DeqhsAbsLint`. -/
theorem deqhsAbsInt : UnforcedLeray.Short.IIb.DeqhsAbsInt :=
  deqhsAbsInt_of deqhsAbsMeas deqhsAbsLint

end UnforcedLeray.Short.IIb
