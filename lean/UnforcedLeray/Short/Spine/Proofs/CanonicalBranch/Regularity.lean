import UnforcedLeray.Short.Spine.Sub.SP_CAN4
import UnforcedLeray.Short.PartI.Tasks.GreenEllipticRegularity
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Bootstrap
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation

/-!
# Spine: `Cons.G3b.ClassicalRegularityHyp`, unconditional final assembly (task `Spine:SP-CAN/4`;
blueprint B0124)

Source of record: `the November 2 reference manuscript`, line 1086 and lines
1134-1145.

Composes the conditional theorem `classicalRegularityHyp_of` (`Sub/SP_CAN4.lean`) with:

* the global elliptic regularity `Short.PartI.greenEllipticRegularity` (task `PartI:C09`), supplying
  `GreenAll`;
* the five proved steps `mildSpatialSmoothing`, `mildIsStrong`, `strongBootstrap`,
  `sobolevJointSmooth`, `smoothRepresentativeEquation` (`Regularity/*.lean`).

No hypothesis is added and no statement is weakened. No `sorry`, `admit`, `axiom` or
`native_decide`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.Spine

/-- **`Spine:SP-CAN/4`**: the classical regularity hypothesis of the canonical branch, with no
hypothesis left open. -/
theorem classicalRegularityHyp : UnforcedLeray.Cons.G3b.ClassicalRegularityHyp :=
  classicalRegularityHyp_of UnforcedLeray.Short.PartI.greenEllipticRegularity
    mildSpatialSmoothing mildIsStrong strongBootstrap sobolevJointSmooth
    smoothRepresentativeEquation

end UnforcedLeray.Short.Spine
