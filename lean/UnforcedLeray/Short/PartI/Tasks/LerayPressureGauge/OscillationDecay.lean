import UnforcedLeray.Short.PartI.Sub.T02_2_4
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.OscMeanLap
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.SliceEnergyIdentity
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.SliceWirtinger
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.GoodSliceSup
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.SlabBound

/-!
# Part I, task `PartI:T02/2/4`: `OscillationDecay` (final assembly)

Source of record: `the November 2 reference manuscript`, line 447 ("The decaying
pressure gauge is used here"; the oscillating part `p - p̄` of the bounded periodic pressure tends
to `0` because `Δp → 0`).

The unconditional theorem `oscillationDecay : OscillationDecay` is obtained by composing the
conditional decomposition of `Sub/T02_2_4.lean` with the five leaf statements `oscMeanLap`,
`sliceEnergyIdentity`, `sliceWirtinger`, `goodSliceSup` and `slabBound`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **`OscillationDecay`** (source line 447): a bounded `C²` function `u`, `c`-periodic in `q`,
with `Δu → 0` as `|η| → ∞`, satisfies `u - ū → 0` as `|η| → ∞`. -/
theorem oscillationDecay : OscillationDecay :=
  oscillationDecay_of (oscMeanReduction_of oscMeanLap) (zeroMeanSliceEnergyDecay_of sliceEnergyIdentity sliceWirtinger)
    (zeroMeanPointwiseFromEnergy_of goodSliceSup slabBound)

end UnforcedLeray.Short.PartI
