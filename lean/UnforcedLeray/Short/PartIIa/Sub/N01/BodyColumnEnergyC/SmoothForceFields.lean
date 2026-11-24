import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields.Repr
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields.Congr
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields.Entrance
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields.Energy

/-!
# `PartII-a:N01/9/1/2` (assembly): `SmoothForceFields`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.  The four proved hypotheses of
`smoothForceFields_of` (`smoothForceRepr`, `velFAeCongr`, `r0Entrance`, `heatIntEnergy`) are
fed to that assembly theorem.
-/

set_option autoImplicit false

theorem smoothForceFields : UnforcedLeray.Short.PartIIa.N01.SmoothForceFields :=
  UnforcedLeray.Short.PartIIa.N01.smoothForceFields_of
    UnforcedLeray.Short.PartIIa.N01.smoothForceRepr
    UnforcedLeray.Short.PartIIa.N01.velFAeCongr
    UnforcedLeray.Short.PartIIa.N01.r0Entrance
    UnforcedLeray.Short.PartIIa.N01.heatIntEnergy
