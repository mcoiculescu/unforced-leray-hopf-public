import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceGradBound
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyClosure

/-!
# `PartII-a:N01/9/1`: `BodyColumnEnergyC`

Source `the November 2 reference manuscript`,
lines 1196-1896 (body column energy). The four leaves are proved in the
`BodyColumnEnergyC/` folder and are fed to `bodyColumnEnergyC_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem bodyColumnEnergyC : UnforcedLeray.Short.PartIIa.N01.BodyColumnEnergyC :=
  bodyColumnEnergyC_of smoothForceDense smoothForceFields smoothForceGradBound energyClosure

end UnforcedLeray.Short.PartIIa.N01
