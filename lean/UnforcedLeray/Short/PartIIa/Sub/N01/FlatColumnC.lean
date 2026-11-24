import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnWeakC

/-!
# `PartII-a:N01/9`: `FlatColumnC`

Source `the November 2 reference manuscript`,
lines 1650-1658, 1669-1674, 1684-1689. Composes `bodyColumnEnergyC` and `bodyColumnWeakC`
through `flatColumnC_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem flatColumnC : UnforcedLeray.Short.PartIIa.N01.FlatColumnC :=
  flatColumnC_of bodyColumnEnergyC bodyColumnWeakC

end UnforcedLeray.Short.PartIIa.N01
