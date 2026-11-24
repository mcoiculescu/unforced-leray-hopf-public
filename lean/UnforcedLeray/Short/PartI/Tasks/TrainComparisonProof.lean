import UnforcedLeray.Short.PartI.Tasks.ComparisonBootstrap

/-!
# `PartI:T10`: `TrainComparison` assembled

Source of record: `the November 2 reference manuscript`, lines 337-355.
The comparison estimate is `train_comparison` (`Tasks/ComparisonBootstrap.lean`, task T09),
whose statement is `TrainComparison`; the quantifiers over `ρ`, `j`, `ν₀`, `tr` in
`TrainComparison` already carry the smallness choices, so this file only restates it.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem trainComparison_proof : TrainComparison :=
  train_comparison

end UnforcedLeray.Short.PartI
