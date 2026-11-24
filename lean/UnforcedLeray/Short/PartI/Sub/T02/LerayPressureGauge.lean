import UnforcedLeray.Short.PartI.Sub.T02_2
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressurePoisson
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.FderivTendstoZero
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureMeanIdentity
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureGaugeSmooth

/-!
# Part I, task `PartI:T02/2`: the decaying pressure gauge (unconditional)

Source of record: `the November 2 reference manuscript`, line 447 and line 277.

The six leaf statements `PressurePoisson`, `FderivTendstoZero`, `PressureBounded`,
`OscillationDecay`, `PressureMeanIdentity`, `PressureGaugeSmooth` are proved in
`Short/PartI/Tasks/LerayPressureGauge/`. This file composes them through `lerayPressureGauge_of`
(`Short/PartI/Sub/T02_2.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **The decaying pressure gauge** (source line 447): a classical solution with bounded
derivatives and decaying velocity has a classical pressure that tends to `0` as `|η| → ∞`. -/
theorem lerayPressureGauge : LerayPressureGauge :=
  lerayPressureGauge_of pressurePoisson fderivTendstoZero pressureBounded oscillationDecay
    pressureMeanIdentity pressureGaugeSmooth

end UnforcedLeray.Short.PartI
