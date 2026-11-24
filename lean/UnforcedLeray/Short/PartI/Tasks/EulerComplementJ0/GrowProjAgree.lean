import UnforcedLeray.Short.PartI.Sub.PartI_S15_2
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0.GrowProjAgree.DualBounded
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0.GrowProjAgree.XgEmbDense

/-!
# Part I, task `PartI:S15/2`: `seedGrowProjAgree`

Assembly of the two leaves `PartI:S15/2/1` (`seedDualBounded`) and `PartI:S15/2/2`
(`xgEmbDense`) through `seedGrowProjAgree_of` (Sub/PartI_S15_2.lean).

Source of record: `the November 2 reference manuscript` lines 603-609 and 841-889.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target.** Resolvents, hence Riesz projections, of the growing mode agree on the seed. -/
theorem seedGrowProjAgree : SeedGrowProjAgree :=
  seedGrowProjAgree_of seedDualBounded xgEmbDense

end UnforcedLeray.Short.PartI
