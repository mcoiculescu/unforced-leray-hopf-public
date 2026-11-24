import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.PartialDeriv
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.L0Classical
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.DClassical
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.AeContinuous
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.Smoothness

/-!
# Spine: `SmoothRepresentativeEquation` (final assembly of `Spine:SP-CAN/4/5`)

Source of record: `the November 2 reference manuscript`, line 1086.

Composes the five proved leaves (`PartialDeriv`, `L0Classical`, `DClassical`, `AeContinuous`,
`Smoothness`) with the conditional theorem `smoothRepresentativeEquation_of`
(`Sub/SP_CAN4_5.lean`). No new hypotheses, no weakening. No `sorry`, `admit`, `axiom` or
`native_decide`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.Spine

/-- **`SmoothRepresentativeEquation`**, proved from the five leaf theorems. -/
theorem smoothRepresentativeEquation : UnforcedLeray.Short.Spine.SmoothRepresentativeEquation :=
  smoothRepresentativeEquation_of partialDerivAe_proof l0ClassicalAe_proof dClassicalAe_proof
    aeEqOfContinuousOn_proof smoothnessFacts_proof

end UnforcedLeray.Short.Spine

end
