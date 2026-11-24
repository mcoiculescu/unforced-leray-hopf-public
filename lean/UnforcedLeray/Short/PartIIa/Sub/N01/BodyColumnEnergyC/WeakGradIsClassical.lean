import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_2
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular

/-!
# `PartII-a:N01/9/1/3/3/2/2` (draft): `WeakGradIsClassical`

Source `the November 2 reference manuscript`
lines 3426-3430.  Discharges the `WeakGradIsClassical` proposition from the regularity of the
heat integral, `heatIntRegular`, via `weakGradIsClassical_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem weakGradIsClassical : UnforcedLeray.Short.PartIIa.N01.WeakGradIsClassical :=
  weakGradIsClassical_of heatIntRegular

end UnforcedLeray.Short.PartIIa.N01
