import UnforcedLeray.Short.Spine.Sub.SP_CAN
import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalModeDPairing

/-!


Source of record: `the November 2 reference manuscript`, lines 970-975,
`kappa = ell(Dq)`. The Prop `WholeLineModeKappa` and its docstring are in
`Short/Spine/Sub/SP_CAN.lean`.

The seed constant is `seedKappa (innerSL ℂ (qdagMode hF)) (qMode hF) _ = innerSL ℂ (qdagMode hF)
(B0094.D ⟨qMode hF, _⟩)`, and the right-hand side is `kapMode c F`. The identity between them is
the closed oscillator pairing `closedD_pairing_rightMode_eq_kapMode`
(`Cons/L2/CanonicalBranch/CanonicalModeDPairing.lean`), which is the Bridge 2 argument in
`CanonicalModeDPairing`. This file only unfolds the seed constant and applies that identity.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.B0010 UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

namespace UnforcedLeray.Short.Spine

/-- **Bridge 2** (`WholeLineModeKappa`, lines 970-975): the Part I constant `κ = ℓ(Dq)` of the
whole-line mode equals `kapMode c F`. -/
theorem wholeLineModeKappa : WholeLineModeKappa := by
  unfold WholeLineModeKappa
  intro c F hF
  unfold PartI.seedKappa
  rw [innerSL_apply_apply]
  exact closedD_pairing_rightMode_eq_kapMode hF

end UnforcedLeray.Short.Spine
