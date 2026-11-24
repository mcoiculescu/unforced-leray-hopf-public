import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields.Repr
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields.Congr
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields.Entrance
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields.Energy
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.WeakGradIsClassical

/-!
# `PartII-a:N01/9/1/3/3/2` (assembly): `smoothClassicalEnergyBound`

Source `the November 2 reference manuscript`
lines 1684-1689, 3541-3552.  The four proved hypotheses of `smoothClassicalEnergyBound_of`
(`smoothForceRepr`, `velFAeCongr`, `r0Entrance`, `heatIntEnergy`) and the two proved classical
inputs (`classicalGradBound`, `weakGradIsClassical`) are fed to that assembly theorem.
-/

set_option autoImplicit false

theorem smoothClassicalEnergyBound : UnforcedLeray.Short.PartIIa.N01.SmoothClassicalEnergyBound :=
  UnforcedLeray.Short.PartIIa.N01.smoothClassicalEnergyBound_of
    UnforcedLeray.Short.PartIIa.N01.smoothForceRepr
    UnforcedLeray.Short.PartIIa.N01.velFAeCongr
    UnforcedLeray.Short.PartIIa.N01.r0Entrance
    UnforcedLeray.Short.PartIIa.N01.heatIntEnergy
    classicalGradBound
    UnforcedLeray.Short.PartIIa.N01.weakGradIsClassical
