import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_2
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnWeakC.WeakAllForces
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnWeakC.WeakProjectionInvisible

/-!
# `PartII-a:N01/9/2`: `BodyColumnWeakC`

Source `the November 2 reference manuscript`,
lines 1650-1658, 1669-1674, 1684-1689 (body column weak equation). Composes
`bodyColumnEnergyC`, `weakAllForces`, and `weakProjectionInvisible` through `bodyColumnWeakC_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem bodyColumnWeakC : UnforcedLeray.Short.PartIIa.N01.BodyColumnWeakC :=
  bodyColumnWeakC_of bodyColumnEnergyC weakAllForces weakProjectionInvisible

end UnforcedLeray.Short.PartIIa.N01
