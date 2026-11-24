import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.ClassicalToWeakFlat
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.FlatOrthSwap

/-!
# Part III-a, task `PartIII-a:T18/2/4` (`NiceForceSolution`): assembly

Target: `niceForceSolution : NiceForceSolution` (`Sub/T18_2.lean`, SP 3427-3440): for every nice
force there is a causal zero-entrance energy solution of the free equation.
Proof: apply the conditional wiring `niceForceSolution_of` (`Sub/T18_2_4.lean`) to the four
unconditional leaves `heatCellClassical`, `lerayProjectSlices`, `classicalToWeakFlat`,
`flatOrthSwap`, each proved in its own module under `NiceForceSolution/`.
Source of record: `the November 2 reference manuscript`, lines 3427-3440.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem niceForceSolution : UnforcedLeray.Short.IIIa.NiceForceSolution :=
  niceForceSolution_of heatCellClassical lerayProjectSlices classicalToWeakFlat flatOrthSwap

end UnforcedLeray.Short.IIIa

end
