import UnforcedLeray.Short.PartI.Sub.T02_1_4
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepFiniteEnergy
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepInitial
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepSolenoidal
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.JointSmoothOfHk
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray

/-!
# Part I, task `PartI:T02/1/4`: `TimeSmoothLeray` (assembly)

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `TimeSmoothLeray` (`Short/PartI/Sub/T02_1.lean`, line 126).  This file is pure assembly:
`timeSmoothLeray_of` (`Short/PartI/Sub/T02_1_4.lean`) applied to `hkPersistence` (task
`PartI:T02/1/2`) and the six leaves `repFiniteEnergy`, `repInitial`, `repSolenoidal`,
`mildPathTimeSmooth`, `jointSmoothOfHk`, `repLeray` (tasks `PartI:T02/1/4/1` ... `/6`).

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem timeSmoothLeray : TimeSmoothLeray :=
  timeSmoothLeray_of hkPersistence repFiniteEnergy repInitial repSolenoidal
    mildPathTimeSmooth jointSmoothOfHk repLeray

end UnforcedLeray.Short.PartI
