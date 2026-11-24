import UnforcedLeray.Lib.ComplexODE.CauchyKernelLog

/-!
# Quantitative L¹ dependence on the log scale (INF18 O3, bypass B8 (ii) form)

Wave 1 block 1H part 3, scoping note

"the L¹ dependence gives `sup |F - N| ≤ C (|α² - β²| + |z| log(1/Im z))`"; §6 risk 2 (explicit
constants for the bifurcation O4). Blueprint unit B0034 (`paper/main.tex` lines 1011--1021).

Combining `norm_normalizedPair_sub_neutral_le` (O3) with the logarithmic kernel bound
`exists_integral_Wlog_div_norm_le_log`: for `0 < Im c ≤ 1`, with
`Q = |β² - α²| + |c - a_*| (1 + log (1/Im c))`, the normalized Rayleigh pair differs from the
normalized neutral pair on `[a, b]` by at most `C Q e^{C Q}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Interval

namespace UnforcedLeray.Rayleigh.Evans

open UnforcedLeray.ComplexODE Sturm GaussianPotential

/-- The perturbation size on the logarithmic scale. -/
def neutralLogSize (α β : ℝ) (c : ℂ) : ℝ :=
  |β ^ 2 - α ^ 2| + ‖c - (gaussianCriticalSpeed : ℂ)‖ * (1 + Real.log (1 / c.im))

theorem neutralLogSize_nonneg (α β : ℝ) {c : ℂ} (hc : 0 < c.im) (hc1 : c.im ≤ 1) :
    0 ≤ neutralLogSize α β c := by
  have hlog : 0 ≤ Real.log (1 / c.im) := Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
  unfold neutralLogSize
  positivity

/-- The L¹ size of the coefficient perturbation is controlled by the logarithmic size. -/
theorem exists_neutralPerturbationSize_le_log {a b : ℝ} (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ (α β : ℝ) (c : ℂ), 0 < c.im → c.im ≤ 1 →
      neutralPerturbationSize α β a b c ≤ C * neutralLogSize α β c := by
  obtain ⟨Cl, hCl, hlog⟩ := exists_integral_Wlog_div_norm_le_log hab
  refine ⟨max (b - a) Cl, le_max_of_le_right hCl, fun α β c hc hc1 => ?_⟩
  have h1 : |β ^ 2 - α ^ 2| * (b - a) ≤ max (b - a) Cl * |β ^ 2 - α ^ 2| := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  have hlog0 : 0 ≤ 1 + Real.log (1 / c.im) := by
    have : 0 ≤ Real.log (1 / c.im) := Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
    linarith
  have h2 : ‖c - (gaussianCriticalSpeed : ℂ)‖ *
      (∫ s in a..b, Wlog s / ‖(neutralOmega s : ℂ) - c‖) ≤
      max (b - a) Cl * (‖c - (gaussianCriticalSpeed : ℂ)‖ * (1 + Real.log (1 / c.im))) := by
    calc ‖c - (gaussianCriticalSpeed : ℂ)‖ * (∫ s in a..b, Wlog s / ‖(neutralOmega s : ℂ) - c‖)
        ≤ ‖c - (gaussianCriticalSpeed : ℂ)‖ * (Cl * (1 + Real.log (1 / c.im))) :=
          mul_le_mul_of_nonneg_left (hlog c hc hc1) (norm_nonneg _)
      _ ≤ ‖c - (gaussianCriticalSpeed : ℂ)‖ * (max (b - a) Cl * (1 + Real.log (1 / c.im))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog0) (norm_nonneg _)
      _ = _ := by ring
  unfold neutralPerturbationSize neutralLogSize
  rw [mul_add]
  exact add_le_add h1 h2

/-- **INF18 O3, logarithmic form.** On `[a, b]`, for fixed `α`, there is `C ≥ 0` such that for
every `β` and every `c` with `0 < Im c ≤ 1`, uniformly on `[a, b]`,
`|(F_β(c) - N_α, F_β(c)' - N_α')| ≤ C Q e^{C Q}`,
`Q = |β² - α²| + |c - a_*| (1 + log (1/Im c))`. -/
theorem norm_normalizedPair_sub_neutral_le_log (α : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ (β : ℝ) (c : ℂ), 0 < c.im → c.im ≤ 1 → ∀ t ∈ Icc a b,
      ‖(normalizedF β a c t - neutralNormalizedF α a t,
          normalizedDerivative β a c t - neutralNormalizedDerivative α a t)‖ ≤
        C * neutralLogSize α β c * Real.exp (C * neutralLogSize α β c) := by
  obtain ⟨C₀, hC₀, hbound⟩ := norm_normalizedPair_sub_neutral_le α hab
  obtain ⟨C₃, hC₃, hsize⟩ := exists_neutralPerturbationSize_le_log hab
  refine ⟨max (C₀ * C₃) C₃, le_max_of_le_right hC₃, fun β c hc hc1 t ht => ?_⟩
  set P := neutralPerturbationSize α β a b c with hP
  set Q := neutralLogSize α β c with hQ
  have hP0 : 0 ≤ P := neutralPerturbationSize_nonneg α β hab c
  have hQ0 : 0 ≤ Q := neutralLogSize_nonneg α β hc hc1
  have hPQ : P ≤ C₃ * Q := hsize α β c hc hc1
  have hM1 : C₀ * C₃ ≤ max (C₀ * C₃) C₃ := le_max_left _ _
  have hM2 : C₃ ≤ max (C₀ * C₃) C₃ := le_max_right _ _
  calc _ ≤ C₀ * P * Real.exp P := hbound β c hc t ht
    _ ≤ C₀ * (C₃ * Q) * Real.exp (C₃ * Q) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hPQ hC₀) (Real.exp_le_exp.mpr hPQ)
          (Real.exp_pos _).le (mul_nonneg hC₀ (mul_nonneg hC₃ hQ0))
    _ = (C₀ * C₃) * Q * Real.exp (C₃ * Q) := by ring
    _ ≤ max (C₀ * C₃) C₃ * Q * Real.exp (max (C₀ * C₃) C₃ * Q) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hM1 hQ0)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hM2 hQ0)) (Real.exp_pos _).le
        exact mul_nonneg (le_max_of_le_right hC₃) hQ0

end UnforcedLeray.Rayleigh.Evans
