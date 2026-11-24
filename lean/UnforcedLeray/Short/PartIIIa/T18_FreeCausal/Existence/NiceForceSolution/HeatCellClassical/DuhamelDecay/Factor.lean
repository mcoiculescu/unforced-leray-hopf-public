import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_4

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/4/2`: the planar heat kernel factorises

Target: `duhDecFactor : DuhDecFactor` (`Sub/PartIIIa_T18_2_4_1_4.lean`, leaf 2 of the Duhamel
decay; SP 3427-3440 of `the November 2 reference manuscript`).

`B0284.heatKernel2 θ w` is by definition `B0191.heatKernel 1 θ w.1 * B0191.heatKernel 1 θ w.2`
(`Units/B0284/Defs.lean`), so the factorisation is definitional.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem duhDecFactor : UnforcedLeray.Short.IIIa.DuhDecFactor := by
  intro θ _ z
  rfl

end UnforcedLeray.Short.IIIa
