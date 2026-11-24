import UnforcedLeray.Short.PartIIb.Sub.T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceAe
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceIdentity
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.Swap

/-!
# Part II-b, task `PartII-b:T12/7` (`DuhamelEquation`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

Assembles the causal Duhamel equation from its three input leaves
`DeqSliceAe` (`PartII-b:T12/7/1`), `DeqSliceIdentity` (`PartII-b:T12/7/6`) and
`DeqSwap` (`PartII-b:T12/7/8`) via `duhamelEquation_of` (`Sub/T12_7.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7`** (`DuhamelEquation`): the Duhamel integral solves the planar
equation weakly; assembled from the leaves `deqSliceAe`, `deqSliceIdentity`, `deqSwap`. -/
theorem duhamelEquation : UnforcedLeray.Short.IIb.DuhamelEquation :=
  duhamelEquation_of deqSliceAe deqSliceIdentity deqSwap

end UnforcedLeray.Short.IIb

end
