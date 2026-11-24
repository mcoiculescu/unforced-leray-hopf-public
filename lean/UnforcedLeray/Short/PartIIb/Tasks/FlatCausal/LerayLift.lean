import UnforcedLeray.Short.PartIIb.Sub.T12_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePeriodicRep
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SliceCylLpAe
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SliceJointHelmholtz
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SliceNormBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SliceWeakSolenoidal
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePerpPlanar

/-!
# Part II-b, task `PartII-b:T12/2` (`FlatLerayLiftOfSlice`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1926 (`P_0` applied at
each age). Target: `FlatLerayLiftOfSlice : CylinderHelmholtzLr → FlatLerayHr` (`Sub/T12.lean`).

The six sub-lemma proofs (`LerayLift/1`-`LerayLift/6`) are imported from their files in
`Tasks/FlatCausal/LerayLift/`, and the conditional assembly `flatLerayLiftOfSlice_of` from
`Sub/T12_2.lean` is applied to them. No placeholder proofs and no added hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem flatLerayLiftOfSlice : UnforcedLeray.Short.IIb.FlatLerayLiftOfSlice :=
  UnforcedLeray.Short.IIb.LerayLiftSub.flatLerayLiftOfSlice_of
    UnforcedLeray.Short.IIb.LerayLiftSub.slicePeriodicRep_proof
    UnforcedLeray.Short.IIb.sliceCylLpAe_proof
    UnforcedLeray.Short.IIb.sliceJointHelmholtz_proof
    UnforcedLeray.Short.IIb.sliceNormBound_proof
    UnforcedLeray.Short.IIb.sliceWeakSolenoidal_proof
    UnforcedLeray.Short.IIb.slicePerpPlanar_proof

end UnforcedLeray.Short.IIb
