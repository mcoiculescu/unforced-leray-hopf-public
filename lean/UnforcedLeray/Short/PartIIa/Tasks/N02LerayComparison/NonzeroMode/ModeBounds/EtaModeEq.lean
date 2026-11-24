import UnforcedLeray.Short.PartIIa.Sub.N02_4_7
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.EtaMul

/-!
# Part II-a, task `PartII-a:N02/4/7/5` (`nzmbEtaModeEq`): the `j = 1` one-mode system

Source of record: `the November 2 reference manuscript`, lines 1722-1727.
If `(G1, G2)` solves `NzModeEq k A B G1 G2` then `(η G1, η G2)` solves it with data
`(η A - G2, η B + G1)`: multiply the two equations by `η` and use `∂_η(η g) = η ∂_η g + g`
(from `nzmb_eta_fderiv`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem nzmbEtaModeEq : NzmbEtaModeEq := by
  intro k A B G1 G2 h1 h2 h
  unfold NzModeEq at h ⊢
  intro x
  obtain ⟨hA, hB⟩ := h x
  have e1 : fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * G1 y) x (0, 1)
      = (x.2 : ℂ) * fderiv ℝ G1 x (0, 1) + G1 x := by
    rw [nzmb_eta_fderiv G1 h1 x (0, 1)]
    simp
  have e2 : fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * G2 y) x (0, 1)
      = (x.2 : ℂ) * fderiv ℝ G2 x (0, 1) + G2 x := by
    rw [nzmb_eta_fderiv G2 h2 x (0, 1)]
    simp
  constructor
  · show Complex.I * (k : ℂ) * ((x.2 : ℂ) * G1 x)
        - fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * G2 y) x (0, 1)
        = (x.2 : ℂ) * A x - G2 x
    rw [e2]
    linear_combination (x.2 : ℂ) * hA
  · show fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * G1 y) x (0, 1)
        + Complex.I * (k : ℂ) * ((x.2 : ℂ) * G2 x)
        = (x.2 : ℂ) * B x + G1 x
    rw [e1]
    linear_combination (x.2 : ℂ) * hB

end UnforcedLeray.Short.PartIIa
