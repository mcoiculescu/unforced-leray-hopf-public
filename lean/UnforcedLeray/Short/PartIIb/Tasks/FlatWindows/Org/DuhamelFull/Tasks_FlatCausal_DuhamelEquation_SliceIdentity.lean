import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceIdentity
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_PartIIb_T12_7_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_HeatPair
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_PairDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_SliceIdentity_IntegrableIoi
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_SliceIdentity_PhiVanish
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_SliceIdentity_SliceLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_SliceIdentity_Split

/-!
# Part II-b, task `PartII-b:T12/7/6` (`dfe_deqSliceIdentity`): slice identity

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
The statement is discharged by the composition `dfe_deqSliceIdentity_of` (Sub file) applied to the
four leaves `dfe_deqPairSplit`, `dfe_deqPairIntegrableIoi`, `dfe_deqPhiVanish`, `dfe_deqSliceLocInt` and the
leaves `dfe_deqHeatPair`, `dfe_deqPairDeriv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/6`** (SP 1923-1927): `dfe_DeqSliceIdentity` from its leaves. -/
theorem dfe_deqSliceIdentity : UnforcedLeray.Short.IIb.dfe_DeqSliceIdentity :=
  dfe_deqSliceIdentity_of dfe_deqPairSplit dfe_deqPairIntegrableIoi dfe_deqPhiVanish dfe_deqSliceLocInt
    dfe_deqHeatPair dfe_deqPairDeriv

end UnforcedLeray.Short.IIb
