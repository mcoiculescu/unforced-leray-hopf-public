import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.ProfContDiff
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.ProfOde
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.ProfLocalNorm
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.SupBound
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.Bootstrap

/-!
# `OscSmoothRep` (task `Spine:SP-CAN/4/4/1`, final assembly)

Proves `UnforcedLeray.Short.Spine.OscSmoothRep` (`Sub/SP_CAN4_4.lean`), the Hermite level
estimate, by feeding the five accepted leaf statements into the compiled assembly
`oscSmoothRep_of` (`Sub/SP_CAN4_4_1.lean`).

Source of record: `the November 2 reference manuscript`, lines 1086 and 1134-1140.
-/

set_option autoImplicit false

theorem oscSmoothRep_proof : UnforcedLeray.Short.Spine.OscSmoothRep :=
  UnforcedLeray.Short.Spine.oscSmoothRep_of
    UnforcedLeray.Short.Spine.oscProfContDiff_proof
    UnforcedLeray.Short.Spine.oscProfOde_proof
    UnforcedLeray.Short.Spine.oscProfLocalNorm_proof
    UnforcedLeray.Short.Spine.oscSupBound_proof
    oscBootstrap_proof
