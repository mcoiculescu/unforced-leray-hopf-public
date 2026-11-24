import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.SeriesSmooth
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.Coefficients
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.Identify

/-!
# Spine: `SobolevJointSmooth`, final assembly (task `Spine:SP-CAN/4/4`, step 4 of
`ClassicalRegularityHyp`)

Proves `UnforcedLeray.Short.Spine.SobolevJointSmooth` (`Sub/SP_CAN4_4.lean` and `Sub/SP_CAN4.lean`)
by feeding the four proved leaf statements into the conditional theorem `sobolevJointSmooth_of`
(`Sub/SP_CAN4_4.lean`). The leaves are in `Regularity/SobolevJoint/`:

* `oscSmoothRep_proof` (`OscRep.lean`): the Hermite level estimate `OscSmoothRep`;
* `seriesJointSmooth_proof` (`SeriesSmooth.lean`): joint smoothness of the series `SeriesJointSmooth`;
* `coefficientBounds_proof` (`Coefficients.lean`): `CoefficientBounds`;
* `seriesIdentify_proof` (`Identify.lean`): `SeriesIdentify`.

Source of record: `the November 2 reference manuscript`, lines 1086 and 1134-1140.

No hypothesis is added and no statement is weakened.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

theorem sobolevJointSmooth : UnforcedLeray.Short.Spine.SobolevJointSmooth :=
  sobolevJointSmooth_of oscSmoothRep_proof seriesJointSmooth_proof coefficientBounds_proof
    seriesIdentify_proof

end UnforcedLeray.Short.Spine
