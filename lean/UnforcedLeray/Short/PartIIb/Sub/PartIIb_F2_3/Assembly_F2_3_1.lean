import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_3

/-!
# `PartII-b:F2/3/1` (`Sub/PartII-b_F2_3/Assembly_F2_3_1.lean`): `PlanarFrozenEulerStep`

Source of record: `the November 2 reference manuscript` (SP) lines 841-852,
931-953, 2121-2123, 2137-2140, 2145-2171.

Assembles `planarFrozenEulerStep : PlanarFrozenEulerStep` from `planarFrozenEulerStep_of`
(`Sub/PartII-b_F2_3_1.lean`) applied to `planarEulerFamily` (`Sub/PartII-b_F2_3_1_1.lean`),
`planarModesInXm` (`Sub/PartII-b_F2_3_1_2.lean`), and `planarEulerSpectral`
(`Sub/PartII-b_F2_3_1_3.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:F2/3/1`**: assembly of `PlanarFrozenEulerStep`. -/
theorem planarFrozenEulerStep : PlanarFrozenEulerStep :=
  planarFrozenEulerStep_of planarEulerFamily planarModesInXm planarEulerSpectral

end UnforcedLeray.Short.IIb
