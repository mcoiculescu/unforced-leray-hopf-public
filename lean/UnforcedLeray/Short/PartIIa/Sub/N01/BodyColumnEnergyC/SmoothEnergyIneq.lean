import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyGradUnique
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothClassicalEnergyBound

/-!
# `PartII-a:N01/9/1/3/3` (assembly): `smoothEnergyIneq`

Source `the November 2 reference manuscript`
lines 1684-1689, 3426-3430, 3541-3552.  The two proved sub-leaves `energyGradUnique` (a.e.
uniqueness of the weak gradient of an energy field) and `smoothClassicalEnergyBound` (classical
energy bound for smooth forces) are fed to the assembly theorem `smoothEnergyIneq_of`.
-/

set_option autoImplicit false

open UnforcedLeray.Short.PartIIa.N01 (SmoothEnergyIneq smoothEnergyIneq_of energyGradUnique)

theorem smoothEnergyIneq : UnforcedLeray.Short.PartIIa.N01.SmoothEnergyIneq :=
  smoothEnergyIneq_of energyGradUnique smoothClassicalEnergyBound
