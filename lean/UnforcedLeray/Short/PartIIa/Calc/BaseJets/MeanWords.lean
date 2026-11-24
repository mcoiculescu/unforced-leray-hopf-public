import UnforcedLeray.Short.PartIIa.Calc.BaseJets

/-!
# Part II-a, task `PartII-a:R02/8/21`: mean words

Source of record: `the November 2 reference manuscript`, lines 447-459
(`S = a₀ G_{νs} + R₀`) and lines 1267-1268 (`K ∂_η^j G = -(j+1) ∂_η^j G`).
The mean stream splits as `S = R₀ + a₀ G` (`meanFam_eq`); the words of `S` are the words of `R₀`
plus `a₀` times the heat words, so the size of `K^ℓ ∂_η^b S` is `s^{-(1/2 + b/2)}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanCoeff)

theorem meanWords_of (hS : MeanSmoothQ) (hH : HeatWords) (hL : IterCalcLin) (h1 : MeanHeatPart)
    (h2 : MeanRemPart) : WordsW (1 / 2) meanFam := by
  refine ⟨hS.1, hS.2, fun ℓ b => ?_⟩
  have hEq : LateEq (wordW ℓ b meanFam)
      (wordW ℓ b remFam0 + fun (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (x : ProfilePoint) =>
        meanCoeff tr 0 * ((-((b : ℝ) + 1)) ^ ℓ * (partialEta^[b] (heatProfile ν)) x)) := by
    intro ν c hν hc tr htr
    have hR : ContDiffOn ℝ ∞ (remFam0 ν c tr) {x : ProfilePoint | 0 < x.2.2} := by
      have e0 : remFam0 ν c tr = fun y => meanFam ν c tr y - meanCoeff tr 0 * heatProfile ν y := by
        funext y
        have hy := meanFam_eq ν c tr y
        rw [hy]
        ring
      rw [e0]
      have hk : ContDiffOn ℝ ∞ (fun y : ProfilePoint => meanCoeff tr 0 * heatProfile ν y)
          {x : ProfilePoint | 0 < x.2.2} :=
        contDiffOn_const.mul (hH ν hν).1
      exact (hS.1 ν c hν hc tr htr).sub hk
    have hG : ContDiffOn ℝ ∞ (heatProfile ν) {x : ProfilePoint | 0 < x.2.2} := (hH ν hν).1
    have hL2 := hL.2.1 (remFam0 ν c tr) (heatProfile ν) hR hG (meanCoeff tr 0) ℓ b 0
    have e : meanFam ν c tr = fun y => remFam0 ν c tr y + meanCoeff tr 0 * heatProfile ν y :=
      funext (meanFam_eq ν c tr)
    intro x hx
    have e2 : ageOperator^[ℓ] (partialEta^[b] (fun y => remFam0 ν c tr y +
        meanCoeff tr 0 * heatProfile ν y)) x =
        ageOperator^[ℓ] (partialEta^[b] (remFam0 ν c tr)) x +
          meanCoeff tr 0 * ageOperator^[ℓ] (partialEta^[b] (heatProfile ν)) x :=
      hL2 hx
    have e3 : ageOperator^[ℓ] (partialEta^[b] (heatProfile ν)) x =
        (-((b : ℝ) + 1)) ^ ℓ * (partialEta^[b] (heatProfile ν)) x :=
      (hH ν hν).2 ℓ b hx
    show ageOperator^[ℓ] (partialEta^[b] (meanFam ν c tr)) x =
      ageOperator^[ℓ] (partialEta^[b] (remFam0 ν c tr)) x +
        meanCoeff tr 0 * ((-((b : ℝ) + 1)) ^ ℓ * (partialEta^[b] (heatProfile ν)) x)
    rw [e, e2, e3]
  exact WW.congr hEq.symm ((h2 ℓ b).add (h1 ℓ b))

end UnforcedLeray.Short.PartIIa.Jet
