import UnforcedLeray.Short.PartIIa.Sub.R01_1
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff

/-!
# Part II-a, task `PartII-a:R01/1` (leaf): the mean stream is smooth

Source of record: `the November 2 reference manuscript`, lines 397-404: the mean
stream `S = bar psi` is `C^infty` for `s > 0`.

Target: `MeanStreamSmooth` (`Sub/R01_1.lean`) follows from `LateProfileSmooth` (`Sub/R02.lean`)
and `hmeanContDiff` (`Short/PartI/Tasks/TrainMeanEquations/HmeanContDiff.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream)

theorem meanStreamSmooth_of (hS : LateProfileSmooth) : MeanStreamSmooth := by
  intro ν c hν hc tr hb
  have hψ := (hS ν c hν hc tr hb).1
  have hg : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => ((x.2.1, x.2.2, x.1) : ProfilePoint)) :=
    (contDiff_fst.comp contDiff_snd).prodMk
      ((contDiff_snd.comp contDiff_snd).prodMk contDiff_fst)
  have hj : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hψ.comp hg.contDiffOn (fun x hx => hx.1)
  exact UnforcedLeray.Short.PartI.hmeanContDiff c hc (fun s z => tr.ψ s z) hj

end UnforcedLeray.Short.PartIIa
