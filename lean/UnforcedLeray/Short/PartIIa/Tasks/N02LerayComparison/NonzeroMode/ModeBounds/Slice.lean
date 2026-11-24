import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Decay
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.Energy1D

/-!
# Part II-a, task `PartII-a:N02/4/4`, helper for `NzModeBounds`: the energy identity on one `s`-slice

Helper file for `NonzeroMode/ModeBounds.lean`. For smooth `G1, G2` solving the one-mode system
`NzModeEq k A B G1 G2` and with exponentially decaying slices at a fixed `s` (the hypotheses of
`NzEnergy1D`), the slice energy identity holds, with `∂_η` written as `fderiv _ _ (0,1)`.
Applied to `(S^α φ, S^α ψ)` with data `(S^α a, S^α b)` this is step (ii) of the sketch.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Slice energy identity: for each fixed `s`, `∫_η (|A|² + |B|²)(s, η) = ∫_η (k²|G1|² + |∂_η G1|²
+ k²|G2|² + |∂_η G2|²)(s, η)`, `∂_η` being `fderiv _ _ (0,1)`. -/
theorem nzmb_slice_energy (k : ℝ) (A B G1 G2 : ℝ × ℝ → ℂ)
    (hG1 : ContDiff ℝ ∞ G1) (hG2 : ContDiff ℝ ∞ G2)
    (h : NzModeEq k A B G1 G2) (s : ℝ)
    (hdec : ∃ κ C : ℝ, 0 < κ ∧ ∀ t : ℝ,
      ‖G1 (s, t)‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ : ℝ => G1 (s, τ)) t‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖G2 (s, t)‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ : ℝ => G2 (s, τ)) t‖ ≤ C * Real.exp (-κ * |t|)) :
    ∫ t : ℝ, (‖A (s, t)‖ ^ 2 + ‖B (s, t)‖ ^ 2) =
      ∫ t : ℝ, (k ^ 2 * ‖G1 (s, t)‖ ^ 2 + ‖fderiv ℝ G1 (s, t) (0, 1)‖ ^ 2
        + k ^ 2 * ‖G2 (s, t)‖ ^ 2 + ‖fderiv ℝ G2 (s, t) (0, 1)‖ ^ 2) := by
  obtain ⟨κ, C, hκ, hb⟩ := hdec
  unfold NzModeEq at h
  have hd1 : Differentiable ℝ G1 := hG1.differentiable (by simp)
  have hd2 : Differentiable ℝ G2 := hG2.differentiable (by simp)
  have hpair : ContDiff ℝ ∞ (fun τ : ℝ => ((s, τ) : ℝ × ℝ)) :=
    contDiff_const.prodMk contDiff_id
  have hφS : ContDiff ℝ 1 (fun τ : ℝ => G1 (s, τ)) := (hG1.comp hpair).of_le (by simp)
  have hψS : ContDiff ℝ 1 (fun τ : ℝ => G2 (s, τ)) := (hG2.comp hpair).of_le (by simp)
  have hODE1 : ∀ t : ℝ, Complex.I * (k : ℂ) * G1 (s, t)
      - deriv (fun τ : ℝ => G2 (s, τ)) t = A (s, t) := by
    intro t
    rw [nzmb_deriv_slice G2 hd2 s t]
    exact (h (s, t)).1
  have hODE2 : ∀ t : ℝ, deriv (fun τ : ℝ => G1 (s, τ)) t
      + Complex.I * (k : ℂ) * G2 (s, t) = B (s, t) := by
    intro t
    rw [nzmb_deriv_slice G1 hd1 s t]
    exact (h (s, t)).2
  have hE := nzEnergy1D k (fun τ : ℝ => G1 (s, τ)) (fun τ : ℝ => G2 (s, τ))
    (fun τ : ℝ => A (s, τ)) (fun τ : ℝ => B (s, τ)) hφS hψS
    ⟨κ, C, hκ, fun t => ⟨(hb t).1, (hb t).2.1, (hb t).2.2.1, (hb t).2.2.2⟩⟩ hODE1 hODE2
  simp only [nzmb_deriv_slice G1 hd1 s, nzmb_deriv_slice G2 hd2 s] at hE
  exact hE

end UnforcedLeray.Short.PartIIa
