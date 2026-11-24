import UnforcedLeray.Short.PartIIa.Sub.F14_1
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.EnergyD2
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.SolenoidalSolution
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.DivPairing
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.DivLinear

/-!
# Part II-a, `PartII-a:F14/1`: `smoothStressMap`

Source of record: `the November 2 reference manuscript`, lines 1537-1544 and
1488-1500.  The four analytic inputs `smoothStressEnergyD2`, `solenoidalBodySolution`,
`tensorDivPairingLe`, `smoothDivLinear` feed `smoothStressMap_of` (Sub/F14_1.lean).
-/

theorem smoothStressMap : UnforcedLeray.Short.PartIIa.SmoothStressMap :=
  UnforcedLeray.Short.PartIIa.smoothStressMap_of
    UnforcedLeray.Short.PartIIa.smoothStressEnergyD2
    UnforcedLeray.Short.PartIIa.solenoidalBodySolution
    UnforcedLeray.Short.PartIIa.tensorDivPairingLe
    UnforcedLeray.Short.PartIIa.smoothDivLinear
