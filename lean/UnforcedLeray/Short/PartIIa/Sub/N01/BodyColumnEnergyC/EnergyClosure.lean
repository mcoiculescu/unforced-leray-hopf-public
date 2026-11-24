import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_4
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyGradLimit
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyVelLimit
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyLimitLoc
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyLimitDivFree
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyLimitWeakGrad

/-!
# `PartII-a:N01/9/1/4` (assembly): `energyClosure`

Source `the November 2 reference manuscript`
lines 3426-3430. The five leaves (`/1`..`/5`) feed the compiled assembly `energyClosure_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem energyClosure : UnforcedLeray.Short.PartIIa.N01.EnergyClosure :=
  energyClosure_of energyGradLimit energyVelLimit energyLimitLoc energyLimitDivFree
    energyLimitWeakGrad

end UnforcedLeray.Short.PartIIa.N01
