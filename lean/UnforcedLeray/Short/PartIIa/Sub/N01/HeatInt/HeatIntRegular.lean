import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_3
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.Zero
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.ContPos
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.DiffPos
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.FderivCont

/-!
# `PartII-a:N01/9/1/2/4/3` (decomposition): `HeatIntRegular`

Assembles the four heat-integral lemmas (`heatIntZero`, `heatIntContPos`, `heatIntDiffPos`,
`heatIntFderivCont`) into `heatIntRegular` via `heatIntRegular_of`.
Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem heatIntRegular : UnforcedLeray.Short.PartIIa.N01.HeatIntRegular :=
  heatIntRegular_of heatIntZero heatIntContPos heatIntDiffPos heatIntFderivCont

end UnforcedLeray.Short.PartIIa.N01
