import UnforcedLeray.Short.PartIIb.Sub.T12_2_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SliceCylLpAe
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SliceClassPath
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.HelmClassExt
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.AvgRedQId

/-!
# Part II-b, task `PartII-b:T12/2/3` (`SliceJointHelmholtz`): proof

Source of record: `the November 2 reference manuscript`, lines 1923-1926.
Target: `UnforcedLeray.Short.IIb.LerayLiftSub.SliceJointHelmholtz` (`Sub/T12_2.lean`).

Immediate: `sliceJointHelmholtz_of` (`Sub/T12_2_3.lean`) applied to the four sub-lemma proofs
`sliceClassPath_proof`, `sliceCylLpAe_proof`, `helmClassExt_proof`, `avgRedQId_proof`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem sliceJointHelmholtz_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SliceJointHelmholtz :=
  UnforcedLeray.Short.IIb.LerayLiftSub.sliceJointHelmholtz_of
    sliceClassPath_proof sliceCylLpAe_proof helmClassExt_proof avgRedQId_proof

end UnforcedLeray.Short.IIb
