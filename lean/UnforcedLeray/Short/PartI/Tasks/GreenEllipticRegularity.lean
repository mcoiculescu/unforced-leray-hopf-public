import UnforcedLeray.Short.PartI.Sub.C09
import UnforcedLeray.Short.PartI.Sub.C09.GreenWeakPunctured
import UnforcedLeray.Short.PartI.Sub.C09.RemovableOrigin
import UnforcedLeray.Short.PartI.Sub.C09.PlanarGreenL2
import UnforcedLeray.Short.PartI.Sub.C09.PlanarBootstrap

/-!
# Part I, task `PartI:C09`: unconditional global elliptic regularity of the Green inverse

Source of record: `the November 2 reference manuscript`, lines 1139-1143
("For completeness, conjugation by `G^{1/2}` ... The radial Green formula for `Δ₂⁻¹` first
gives `‖Δ₂⁻¹ f‖₂ ≤ C‖f‖_{X_G}`; elliptic regularity ... show `L : X_{G,j} → X_{G,j}` is
bounded.").

This file assembles the unconditional statement `B0122.GreenEllipticRegularity j` from the
four proved ingredients of the `C09` route:

* `greenWeakPunctured` (`Sub/C09/GreenWeakPunctured.lean`): the weak equation on `ℝ² \ {0}`;
* `removableOrigin` (`Sub/C09/RemovableOrigin.lean`): removal of the origin;
* `planarGreenL2` (`Sub/C09/PlanarGreenL2.lean`): the `L²` bounds;
* `planarBootstrap j` (`Sub/C09/PlanarBootstrap.lean`): the bootstrap to all orders.

The glue theorem is `UnforcedLeray.Short.PartI.greenEllipticRegularity_of`
(`Sub/C09.lean`). No hypotheses are added.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **`PartI:C09`**: global elliptic regularity of the Green inverse for every order `j`
(source lines 1139-1143). The statement is `B0122.GreenEllipticRegularity j`
(`Units/B0122.lean`, line 295). -/
theorem greenEllipticRegularity (j : ℕ) : B0122.GreenEllipticRegularity j :=
  UnforcedLeray.Short.PartI.greenEllipticRegularity_of j
    UnforcedLeray.Short.PartI.greenWeakPunctured
    UnforcedLeray.Short.PartI.removableOrigin
    UnforcedLeray.Short.PartI.planarGreenL2
    (UnforcedLeray.Short.PartI.planarBootstrap j)

end UnforcedLeray.Short.PartI
