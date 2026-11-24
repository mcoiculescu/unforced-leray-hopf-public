import UnforcedLeray.Short.Spine.Sub.SP_CAN
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Seed
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Kappa
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Mild
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity
import UnforcedLeray.Short.PartI.Tasks.CanonicalBranchProof

/-!
# Spine: `Cons.C01.CanonicalBranchHyp` (task `Spine:SP-CAN`)

Assembly of the four bridges (`Short/Spine/Sub/SP_CAN.lean`) with Part I's canonical branch
(`PartI:C11`, `PartI.canonicalBranch_proof`). Source of record:
`the November 2 reference manuscript`, `prop:short-canonical` (lines 1075-1150).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

theorem canonicalBranchHyp : UnforcedLeray.Cons.C01.CanonicalBranchHyp :=
  canonicalBranchHyp_of PartI.canonicalBranch_proof wholeLineModeIsSeed wholeLineModeKappa
    strongCanonicalIsMild classicalRegularityHyp

end UnforcedLeray.Short.Spine

theorem canonicalBranchHyp : UnforcedLeray.Cons.C01.CanonicalBranchHyp :=
  UnforcedLeray.Short.Spine.canonicalBranchHyp

#print axioms canonicalBranchHyp
