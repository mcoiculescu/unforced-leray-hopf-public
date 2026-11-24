import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.WeightedInt.Slab
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.WeightedInt.MemLp

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/2`: `DualGWeightedInt`

Source: `the November 2 reference manuscript` lines 1923-1927.
Composition of `dualGWeightedInt_of` with `slabCompare` (WeightedInt/Slab) and
`dualGMemLp` (WeightedInt/MemLp).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem dualGWeightedInt : UnforcedLeray.Short.IIb.DualGWeightedInt :=
  dualGWeightedInt_of slabCompare dualGMemLp

end UnforcedLeray.Short.IIb
