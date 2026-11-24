import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Phase-translation invariance of the normalised `L²_τ` norm (SP 3640-3646)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- A `P`-periodic function has the same lower integral over every period window. -/
theorem lintegral_Ioc_periodic (P : ℝ) (hP : 0 < P) (H : ℝ → ℝ≥0∞)
    (hper : ∀ τ, H (τ + P) = H τ) (t : ℝ) :
    ∫⁻ τ in Ioc t (t + P), H τ = ∫⁻ τ in Ioc 0 (0 + P), H τ := by
  haveI : Fact (0 < P) := ⟨hP⟩
  have hp : Function.Periodic H P := hper
  have h1 := AddCircle.lintegral_preimage P t (hp.lift)
  have h2 := AddCircle.lintegral_preimage P 0 (hp.lift)
  have e : ∀ a : ℝ, hp.lift (a : AddCircle P) = H a := fun a => hp.lift_coe a
  simp only [e] at h1 h2
  rw [h1, h2]

theorem lintegral_Ioc_shift (P : ℝ) (hP : 0 < P) (H : ℝ → ℝ≥0∞)
    (hper : ∀ τ, H (τ + P) = H τ) (s : ℝ) :
    ∫⁻ τ in Ioc 0 P, H (τ + s) = ∫⁻ τ in Ioc 0 P, H τ := by
  have h := lintegral_Ioc_periodic P hP H hper s
  rw [zero_add] at h
  rw [← h, ← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
    ← lintegral_add_right_eq_self (fun x => (Ioc s (s + P)).indicator H x) s]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Ioc 0 P
  · have : x + s ∈ Ioc s (s + P) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [indicator_of_mem hx, indicator_of_mem this]
  · have : x + s ∉ Ioc s (s + P) := fun h' => hx ⟨by linarith [h'.1], by linarith [h'.2]⟩
    rw [indicator_of_notMem hx, indicator_of_notMem this]

/-- Phase invariance of `ltauAt`. -/
theorem ltauAt_shift (P : ℝ) (hP : 0 < P) (G : ℝ → ℝ≥0∞)
    (hper : ∀ τ, G (τ + P) = G τ) (s : ℝ) :
    ltauAt P (fun τ => G (τ + s)) = ltauAt P G := by
  unfold ltauAt
  congr 2
  exact lintegral_Ioc_shift P hP (fun τ => G τ ^ (2:ℝ)) (fun τ => by simp only [hper]) s

end UnforcedLeray.Short.IIIa

end
