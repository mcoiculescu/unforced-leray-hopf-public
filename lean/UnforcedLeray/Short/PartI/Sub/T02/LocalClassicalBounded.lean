import UnforcedLeray.Short.PartI.Sub.T02_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.MildTrainExists
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.FiniteEnergyDecay

/-!
# Part I, task `PartI:T02/1`: unconditional local classical bounded solution

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1, local part).

Assembly of the six accepted leaves `PartI:T02/1/1`-`PartI:T02/1/6` through
`localClassicalBounded_of` (`Short/PartI/Sub/T02_1.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem localClassicalBounded : LocalClassicalBounded :=
  localClassicalBounded_of mildTrainExists hkPersistence spatialRepFromPersistent
    timeSmoothLeray lerayVelocityToClassical finiteEnergyDecay

end UnforcedLeray.Short.PartI
