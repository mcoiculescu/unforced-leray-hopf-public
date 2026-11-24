import UnforcedLeray.Short.PartIIa.Sub.F03_1

/-!


Proves `WindowChartU` of `Short/PartII-a/Sub/F03_1.lean`, unconditionally: with `θ = e^t` and
`x = e^{t/2} y`,
`∫ windowField χ τ₀ W c X * ζ X = ∫ e^{2t} χ(t) W_c(τ₀ + t, y) ζ(e^t, e^{t/2} y) dt dy`.

Source of record: `the November 2 reference manuscript`, lines 1431-1434
(`θ = e^t`, `x = e^{t/2} y`). Chart lemmas: `Units/B0424/Chart.lean` (`integral_expChart`,
`integral_dilChart`, both without integrability hypotheses).

Route: (1) the integrand vanishes off `{θ > 0}`, so the integral is over `Ioi 0 ×ˢ univ`;
(2) `integral_expChart` with `log (exp t) = t`; (3) `integral_dilChart`; (4) the weights
`e^{3t/2} · e^t · e^{-t/2} = e^{2t}` and `e^{-t/2} • e^{t/2} • y = y`.
-/

set_option autoImplicit false

open Set MeasureTheory
open UnforcedLeray.B0424
open UnforcedLeray.PhaseSpace
open UnforcedLeray.Parabolic

namespace UnforcedLeray.Short.PartIIa

/-- The dilation cancels: `e^{-t/2} • (e^{t/2} • y) = y`. -/
theorem wcu_smul_cancel (t : ℝ) (y : Space) :
    Real.exp (-(t / 2)) • (Real.exp (t / 2) • y) = y := by
  rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

/-- The value of `windowField` at `expChart p = (e^{t}, x)` (`log (exp t) = t`, `t = p.1`). -/
theorem wcu_windowField_expChart (χ : ℝ → ℝ) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3)
    (ζ : PS 3 → ℝ) (p : ℝ × Space) :
    windowField χ τ₀ W c (expChart p) * (ζ (expChart p) : ℂ) =
      ((χ p.1 * Real.exp (-(p.1 / 2)) : ℝ) : ℂ) * W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) c *
        (ζ (Real.exp p.1, p.2) : ℂ) := by
  have hpos : 0 < Real.exp p.1 := Real.exp_pos _
  simp only [expChart, windowField, if_pos hpos, Real.log_exp]

/-- **Task `PartII-a:F03/1/4`** (unconditional): the change of variables `θ = e^t`, `x = e^{t/2} y`
on the left side. -/
theorem windowChartU : UnforcedLeray.Short.PartIIa.WindowChartU := by
  intro χ τ₀ W c ζ
  -- (1) the integrand vanishes where `θ ≤ 0`
  have h1 : ∫ X, windowField χ τ₀ W c X * (ζ X : ℂ) =
      ∫ X in Ioi (0 : ℝ) ×ˢ (univ : Set Space), windowField χ τ₀ W c X * (ζ X : ℂ) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro X hX
    have hX1 : ¬ (0 < X.1) := fun h => hX (mem_prod.2 ⟨h, mem_univ _⟩)
    simp [windowField, hX1]
  -- (2) the time change `θ = e^t`
  have h2 : ∫ X in Ioi (0 : ℝ) ×ˢ (univ : Set Space), windowField χ τ₀ W c X * (ζ X : ℂ) =
      ∫ p : ℝ × Space, Real.exp p.1 •
        (windowField χ τ₀ W c (expChart p) * (ζ (expChart p) : ℂ)) :=
    integral_expChart (fun X => windowField χ τ₀ W c X * (ζ X : ℂ))
  -- (3) the pointwise value after `θ = e^t`
  have h3 : ∫ p : ℝ × Space, Real.exp p.1 •
        (windowField χ τ₀ W c (expChart p) * (ζ (expChart p) : ℂ)) =
      ∫ p : ℝ × Space, Real.exp p.1 •
        (((χ p.1 * Real.exp (-(p.1 / 2)) : ℝ) : ℂ) * W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) c *
          (ζ (Real.exp p.1, p.2) : ℂ)) := by
    congr 1
    funext p
    rw [wcu_windowField_expChart]
  -- (4) the dilation `x = e^{t/2} y`
  rw [h1, h2, h3, integral_dilChart (fun p : ℝ × Space => Real.exp p.1 •
        (((χ p.1 * Real.exp (-(p.1 / 2)) : ℝ) : ℂ) * W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2) c *
          (ζ (Real.exp p.1, p.2) : ℂ)))]
  congr 1
  funext p
  have he : Real.exp (2 * p.1) = Real.exp (3 * p.1 / 2) * Real.exp p.1 * Real.exp (-(p.1 / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [dilChart, wcu_smul_cancel, Complex.real_smul]
  rw [he]
  push_cast
  ring

end UnforcedLeray.Short.PartIIa
