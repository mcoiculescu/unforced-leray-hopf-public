import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.SlabDivZero
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntPeriodic
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntDivZero
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.PeriodicWeakDeriv
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntEnergyLoc

/-!
# `PartII-a:N01/9/1/2/4` (assembly): `HeatIntEnergy`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.  The six leaf propositions
(`SlabDivZero`, `HeatIntPeriodic`, `HeatIntRegular`, `HeatIntDivZero`, `PeriodicWeakDeriv`,
`HeatIntEnergyLoc`) are proved in the `HeatInt/` leaf files and are fed to `heatIntEnergy_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem heatIntEnergy : UnforcedLeray.Short.PartIIa.N01.HeatIntEnergy :=
  heatIntEnergy_of slabDivZero heatIntPeriodic heatIntRegular heatIntDivZero periodicWeakDeriv
    heatIntEnergyLoc

end UnforcedLeray.Short.PartIIa.N01
