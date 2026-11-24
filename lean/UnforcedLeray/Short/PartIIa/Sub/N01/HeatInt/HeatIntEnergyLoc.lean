import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_6
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.DerivForceSmooth
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatGradIdentity
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntSliceL2
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntPeriodic
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular

/-!
# `PartII-a:N01/9/1/2/4/6` (decomposition): `HeatIntEnergyLoc`

Assembles the four heat-integral inputs `derivForceSmooth`, `heatGradIdentity`,
`heatIntSliceL2`, `heatIntPeriodic`, `heatIntRegular` into `heatIntEnergyLoc` via
`heatIntEnergyLoc_of`.  Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.
-/

set_option autoImplicit false

noncomputable section

theorem heatIntEnergyLoc : UnforcedLeray.Short.PartIIa.N01.HeatIntEnergyLoc :=
  UnforcedLeray.Short.PartIIa.N01.heatIntEnergyLoc_of
    UnforcedLeray.Short.PartIIa.N01.derivForceSmooth
    UnforcedLeray.Short.PartIIa.N01.heatGradIdentity
    heatIntSliceL2
    heatIntPeriodic
    UnforcedLeray.Short.PartIIa.N01.heatIntRegular
