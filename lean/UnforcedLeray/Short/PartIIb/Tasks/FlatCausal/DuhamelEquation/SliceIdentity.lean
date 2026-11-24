import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceIdentity.Split
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceIdentity.IntegrableIoi
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceIdentity.PhiVanish
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceIdentity.SliceLocInt

/-!
# Part II-b, task `PartII-b:T12/7/6` (`deqSliceIdentity`): slice identity

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
The statement is discharged by the composition `deqSliceIdentity_of` (Sub file) applied to the
four leaves `deqPairSplit`, `deqPairIntegrableIoi`, `deqPhiVanish`, `deqSliceLocInt` and the
leaves `deqHeatPair`, `deqPairDeriv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/6`** (SP 1923-1927): `DeqSliceIdentity` from its leaves. -/
theorem deqSliceIdentity : UnforcedLeray.Short.IIb.DeqSliceIdentity :=
  deqSliceIdentity_of deqPairSplit deqPairIntegrableIoi deqPhiVanish deqSliceLocInt
    deqHeatPair deqPairDeriv

end UnforcedLeray.Short.IIb
