import UnforcedLeray.Short.PartIIb.Sub.T12_7_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm.Leaf.DeqhsAbsInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm.Leaf.DeqhsIdent
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm.Leaf.DeqhsFubini

/-!
# Part II-b, task `PartII-b:T12/7/3` (`DeqHeatSymm`): assembly of the three leaves

Source of record: `the November 2 reference manuscript`, lines 1923-1927 (the heat
semigroup is self-adjoint). The unconditional statement `DeqHeatSymm` follows from the leaves
`deqhsAbsInt` (`/1`), `deqhsIdent` (`/2`) and `deqhsFubini` (`/3`) via `deqHeatSymm_of`
(`Sub/T12_7_3.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/3`** (SP 1923-1927): self-adjointness of the flat heat semigroup,
assembled from the three leaves. -/
theorem deqHeatSymm : UnforcedLeray.Short.IIb.DeqHeatSymm :=
  deqHeatSymm_of deqhsAbsInt deqhsIdent deqhsFubini

end UnforcedLeray.Short.IIb
