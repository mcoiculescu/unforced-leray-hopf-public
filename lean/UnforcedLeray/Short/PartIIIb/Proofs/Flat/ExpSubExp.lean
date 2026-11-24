import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Norm

/-!
# Proof of `expSubExpLe` (source: `the November 2 reference manuscript`, lines 4655-4658)

Comparison of `e^{-λ z}` with `e^{-λ t}` for `z ≤ t`: by the mean value inequality on `[z,t]`,
the derivative of `s ↦ e^{-λ s}` is `-λ e^{-λ s}`, of norm `‖λ‖ e^{-Re λ · s} ≤ ‖λ‖ e^{-Re λ · z}`
for `s ≥ z` (since `Re λ ≥ 0`).
-/

namespace UnforcedLeray.Short.PartIIIb.ConcreteYF

open Filter Topology Set

theorem expSubExpLe (lam : ℂ) (hlam : 0 ≤ lam.re) (z t : ℝ) (hzt : z ≤ t) : ‖Complex.exp (-lam * (z : ℂ)) - Complex.exp (-lam * (t : ℂ))‖ ≤ ‖lam‖ * (t - z) * Real.exp (-lam.re * z) := by
  set f : ℝ → ℂ := fun s => Complex.exp (-lam * (s : ℂ)) with hf
  have hd : ∀ s : ℝ, HasDerivAt f (Complex.exp (-lam * (s : ℂ)) * (-lam)) s := by
    intro s
    have h := ((hasDerivAt_id s).ofReal_comp.const_mul (-lam)).cexp
    exact h.congr_deriv (by simp)
  have hbound : ∀ s ∈ Icc z t, ‖deriv f s‖ ≤ ‖lam‖ * Real.exp (-lam.re * z) := by
    intro s hs
    rw [(hd s).deriv]
    have hre : (-lam * (s : ℂ)).re = -lam.re * s := by simp
    rw [norm_mul, Complex.norm_exp, hre, norm_neg]
    have hexp : Real.exp (-lam.re * s) ≤ Real.exp (-lam.re * z) := by
      apply Real.exp_le_exp.2
      have := mul_nonneg hlam (sub_nonneg.2 hs.1)
      nlinarith
    have hn : 0 ≤ ‖lam‖ := norm_nonneg lam
    nlinarith [Real.exp_pos (-lam.re * s)]
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Icc z t) (C := ‖lam‖ * Real.exp (-lam.re * z))
    (fun s _ => (hd s).differentiableAt) hbound (convex_Icc z t) (left_mem_Icc.2 hzt) (right_mem_Icc.2 hzt)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hzt)] at hmv
  have e1 : Complex.exp (-lam * (z : ℂ)) = f z := rfl
  have e2 : Complex.exp (-lam * (t : ℂ)) = f t := rfl
  rw [e1, e2, norm_sub_rev]
  calc ‖f t - f z‖ ≤ ‖lam‖ * Real.exp (-lam.re * z) * (t - z) := hmv
    _ = ‖lam‖ * (t - z) * Real.exp (-lam.re * z) := by ring

end UnforcedLeray.Short.PartIIIb.ConcreteYF
