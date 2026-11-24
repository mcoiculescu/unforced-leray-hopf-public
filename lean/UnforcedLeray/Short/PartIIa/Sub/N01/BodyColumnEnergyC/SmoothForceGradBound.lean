import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyFieldSub
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.VelFAeTransfer
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothEnergyIneq

/-!
# `PartII-a:N01/9/1/3`: `smoothForceGradBound`

Assembly of the three leaf theorems `energyFieldSub` (`PartII-a:N01/9/1/3/1`),
`velFAeTransfer` (`PartII-a:N01/9/1/3/2`) and `smoothEnergyIneq` (`PartII-a:N01/9/1/3/3`)
into `smoothForceGradBound_of`.
-/

set_option autoImplicit false

theorem smoothForceGradBound : UnforcedLeray.Short.PartIIa.N01.SmoothForceGradBound :=
  UnforcedLeray.Short.PartIIa.N01.smoothForceGradBound_of
    UnforcedLeray.Short.PartIIa.N01.energyFieldSub
    UnforcedLeray.Short.PartIIa.N01.velFAeTransfer
    smoothEnergyIneq
