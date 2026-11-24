import UnforcedLeray.Short.Spine.Sub.SP_CAN4_2
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong.DomainDerivative

/-!
# Spine: `MildIsStrong`, final assembly (task `Spine:SP-CAN/4/2`, step 2 of
`ClassicalRegularityHyp`)

Proves `UnforcedLeray.Short.Spine.MildIsStrong` (`Sub/SP_CAN4.lean`) by feeding the two proved
inputs into the conditional theorem `mildIsStrong_of` (`Sub/SP_CAN4_2.lean`):

* `mildSpatialSmoothing` (`Regularity/Smoothing.lean`, step 1);
* `mildDomainDerivative` (`Regularity/Strong/DomainDerivative.lean`, task `Spine:SP-CAN/4/2/1`).

Source of record: `the November 2 reference manuscript`, line 1086 and lines
1134-1145.

No hypothesis is added and no statement is weakened.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

theorem mildIsStrong : UnforcedLeray.Short.Spine.MildIsStrong :=
  mildIsStrong_of mildSpatialSmoothing mildDomainDerivative

end UnforcedLeray.Short.Spine
