import UnforcedLeray.Short.Spine.Sub.SP_CAN4_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing.XGjIntegral
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing.LogKernel
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing.Base
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing.Continuity
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing.Interpolation
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing.Step

/-!
# Spine: `MildSpatialSmoothing`, final assembly (task `Spine:SP-CAN/4/1`, step 1 of
`ClassicalRegularityHyp`; blueprint B0124)

Target (`Short/Spine/Sub/SP_CAN4_1.lean`): `MildSpatialSmoothing`, i.e. under `GreenAll` a mild
solution takes values in every `X_{G,j}` for `θ > 0` and is continuous into each.

The conditional theorem `mildSpatialSmoothing_of` (`Sub/SP_CAN4_1.lean`) reduces this to the four
leaf statements `MildBase`, `MildLevelStep`, `MildContinuous`, `XGjContinuousOfBounds`. Each leaf is
proved in its own file under `Regularity/Smoothing/` (`XGjIntegral`, `LogKernel`, `Base`,
`Continuity`, `Interpolation`, `Step`). This file only composes them; no hypothesis is added.

Source of record: `the November 2 reference manuscript`, line 1086 and lines
1134-1145.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.Spine

/-- **Step 1, smoothing** (shorter proof lines 1086 and 1134-1145): a mild solution takes values
in every `X_{G,j}` for `θ > 0` and is continuous into each. Proved by
`mildSpatialSmoothing_of mildBase_proof mildLevelStep_proof mildContinuous_proof
xgjContinuousOfBounds_proof`. -/
theorem mildSpatialSmoothing : UnforcedLeray.Short.Spine.MildSpatialSmoothing :=
  mildSpatialSmoothing_of mildBase_proof mildLevelStep_proof mildContinuous_proof
    xgjContinuousOfBounds_proof

end UnforcedLeray.Short.Spine
