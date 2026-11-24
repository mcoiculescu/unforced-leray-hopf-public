import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc
import UnforcedLeray.Short.PartIIa.Sub.R02_2
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ProfileDict

/-!
# Part II-a, block `A₂`, task `PartII-a:R02/12/6`: the mean equation in profile variables

Source: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`:
`S_s - νS_ηη = g`, line 399).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet.A2

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (IsBUCTrain meanStream meanStress)

/-- **The mean equation in profile variables** (task `PartII-a:R02/12/6`): `(∂_s - ν∂_η²)S = g`
for `s > 0`, from `TrainMeanEquations` (first and second conjuncts) and the profile dictionary. -/
theorem meanHeatEq_of (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) :
    UnforcedLeray.Short.PartIIa.Jet.A2.MeanHeatEq := by
  intro ν c hν hc tr htr x hx
  have hG : ContDiffOn ℝ ∞ (trainProfile fun s z => meanStream tr s z.2)
      {y : ProfilePoint | 0 < y.2.2} :=
    UnforcedLeray.Short.PartIIa.contDiffOn_trainProfile_of_eta
      (G := fun s η => meanStream tr s η) (hE ν c hν hc tr htr).1
  have hAge : partialAge (trainProfile fun s z => meanStream tr s z.2) x
      = deriv (fun r => meanStream tr r x.2.1) x.2.2 := by
    have h := UnforcedLeray.Short.PartIIa.profileDict
      (fun s z => meanStream tr s z.2) hG 0 0 1 x hx
    simp only [Function.iterate_zero, Function.iterate_one, id, iteratedDeriv_zero,
      iteratedDeriv_one] at h
    exact h
  have hEta : partialEta (partialEta (trainProfile fun s z => meanStream tr s z.2)) x
      = deriv (deriv (fun e => meanStream tr x.2.2 e)) x.2.1 := by
    have h := UnforcedLeray.Short.PartIIa.profileDict
      (fun s z => meanStream tr s z.2) hG 2 0 0 x hx
    simp only [Function.iterate_zero, id, iteratedDeriv_zero, iteratedDeriv_succ] at h
    exact h
  have heq := (hE ν c hν hc tr htr).2 x.2.2 hx x.2.1
  show partialAge (trainProfile fun s z => meanStream tr s z.2) x
      - ν * partialEta (partialEta (trainProfile fun s z => meanStream tr s z.2)) x
      = trainProfile (fun s z => meanStress tr s z.2) x
  rw [hAge, hEta]
  exact heq.1

end UnforcedLeray.Short.PartIIa.Jet.A2
