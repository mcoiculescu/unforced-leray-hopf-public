import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_SliceIdentity
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_Swap

/-!
# Part II-b, task `PartII-b:T12/7` (`dfe_DuhamelEquation`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

Assembles the causal Duhamel equation from its three input leaves
`DeqSliceAe` (`PartII-b:T12/7/1`), `dfe_DeqSliceIdentity` (`PartII-b:T12/7/6`) and
`dfe_DeqSwap` (`PartII-b:T12/7/8`) via `dfe_duhamelEquation_of` (`Sub/T12_7.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7`** (`dfe_DuhamelEquation`): the Duhamel integral solves the planar
equation weakly; assembled from the leaves `deqSliceAe`, `dfe_deqSliceIdentity`, `dfe_deqSwap`. -/
theorem dfe_duhamelEquation : UnforcedLeray.Short.IIb.dfe_DuhamelEquation :=
  dfe_duhamelEquation_of deqSliceAe dfe_deqSliceIdentity dfe_deqSwap

end UnforcedLeray.Short.IIb

end
