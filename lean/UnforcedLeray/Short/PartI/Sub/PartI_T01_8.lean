import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV1

/-!
# Part I, task `PartI:T01/8` (audit decomposition)

Source: `the November 2 reference manuscript`, lines 397-404.
`TrainMeanMomentumEta` follows from `TrainMeanStreamDeriv` (`PartI:T01/2`) and `trainMeanV1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- `S_s = g - ν ∂_η \bar v₁` (T01/2) and `∂_η S = -\bar v₁` (T01/1) give
`S_s - ν S_ηη - g ≡ 0`, hence its `η`-derivative vanishes. -/
theorem trainMeanMomentumEta_of (h2 : TrainMeanStreamDeriv) : TrainMeanMomentumEta := by
  intro ν c hν hc tr hbuc s hs η
  have hdS : deriv (fun e => meanStream tr s e) = fun e => -hmean c (fun z => tr.v s z 0) e := by
    funext e
    have h := trainMeanV1 ν c hν hc tr s hs e
    linarith
  have hz : (fun η' => deriv (fun r => meanStream tr r η') s -
        ν * deriv (deriv (fun e => meanStream tr s e)) η' - meanStress tr s η') = fun _ => 0 := by
    funext η'
    have h := h2 ν c hν hc tr hbuc s hs η'
    rw [h, hdS]
    have hn : deriv (fun e => -hmean c (fun z => tr.v s z 0) e) η' =
        -deriv (fun e => hmean c (fun z => tr.v s z 0) e) η' := deriv.neg
    rw [hn]
    ring
  rw [hz]
  exact hasDerivAt_const η 0

end UnforcedLeray.Short.PartI
