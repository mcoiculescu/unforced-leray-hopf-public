import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanStreamDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanVelDecay
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStressDecay

/-!
# Part I, task `PartI:T01/10`: the mean stream has age derivative decaying in `η`

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`).
The statement `TrainMeanStreamTimeDecay` is defined in `Short/PartI/Sub/T01.lean`.

Route (BUC trains). By `trainMeanStreamDeriv` (`PartI:T01/2`), for `s > 0`,
`∂_s S(s,η) = g(s,η) - ν ∂_η \bar v₁(s,η)` for every `η`. Since `g(s,·) → 0` at `+∞`
(`bucMeanStressDecay`, `PartI:TC/4`) and `∂_η \bar v₁(s,·) → 0` at `+∞`
(`bucMeanVelDecay`, `PartI:TC/3`), the difference tends to `0 - ν · 0 = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

/-- **`PartI:T01/10`, `TrainMeanStreamTimeDecay`** (source lines 397-404): for a BUC train and
`s > 0`, the age derivative of the mean stream tends to `0` as `η → +∞`. -/
theorem trainMeanStreamTimeDecay : TrainMeanStreamTimeDecay := by
  intro ν c hν hc tr hbuc s hs
  have hfun : (fun η : ℝ => deriv (fun r => meanStream tr r η) s) =
      fun η => meanStress tr s η - ν * deriv (meanVel1 tr s) η := by
    funext η
    rw [trainMeanStreamDeriv ν c hν hc tr hbuc s hs η]
    rfl
  rw [hfun]
  have h1 : Tendsto (meanStress tr s) atTop (𝓝 0) :=
    bucMeanStressDecay ν c hν hc tr hbuc s hs.le
  have h2 : Tendsto (fun η : ℝ => deriv (meanVel1 tr s) η) atTop (𝓝 0) :=
    (bucMeanVelDecay ν c hν hc tr hbuc s hs.le).2
  have h3 := h1.sub (h2.const_mul ν)
  rw [mul_zero, sub_zero] at h3
  exact h3

end UnforcedLeray.Short.PartI
