import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AZeroBmatLinear.Helpers

/-!
# `AZeroBmatBound`: the Laplace row is bounded by `C M(A)`

Source 4863-4864 ("its Laplace integrand is bounded by `C t^{μ+3/2} e^{-(γ-a_s)t}`"). The
integrand of `a₀(B_{μ,ν}[A])` vanishes for `t > 11/10ν` and is bounded on `(0, 11/10ν]` by
`C' M(A)` (`azInt_bound_Ioc`, from `BmatBound`), so the integral over `(0, 11/10ν]` is at most
`(11/10ν) · C' M(A)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem aZeroBmatBound (as : ℝ) (χf : ℝ → ℝ) : AZeroBmatBound as χf := by
  intro hχ lam ell ν μ hν hμ
  refine ⟨‖ell‖ * (1 + μ) * ((11 / 10 : ℝ) / ν) ^ (μ + 5 / 2) *
    Real.exp (|lam.re| * ((11 / 10 : ℝ) / ν)), fun A hA => ?_⟩
  have hT : 0 < (11 / 10 : ℝ) / ν := div_pos (by norm_num) hν
  have hbd := azInt_ae_le_indicator lam μ (Bmat ν μ χf A) ((11 / 10 : ℝ) / ν) (azK lam μ ν χf A)
    (fun t ht => azInt_zero_of_Bmat_zero lam μ _ t (azBmat_zero hχ μ hν A t ht))
    (fun t ht0 htT => azInt_bound_Ioc hχ μ hν hμ lam A hA t ht0 htT)
  have h1 := norm_integral_le_of_norm_le
    (integrable_indicator_Ioc_const ((11 / 10 : ℝ) / ν) (azK lam μ ν χf A)) hbd
  rw [integral_indicator_const _ measurableSet_Ioc, real_restrict_Ioc_eq _ hT.le,
    smul_eq_mul] at h1
  have hn : ‖-(1 / 2 : ℂ) * ell‖ = 1 / 2 * ‖ell‖ := by
    rw [norm_mul, norm_neg, norm_div, norm_one]
    norm_num
  have hpow : ((11 / 10 : ℝ) / ν) ^ (μ + 5 / 2) =
      ((11 / 10 : ℝ) / ν) ^ μ * ((11 / 10 : ℝ) / ν) ^ (3 / 2 : ℝ) * ((11 / 10 : ℝ) / ν) := by
    rw [show μ + 5 / 2 = μ + 3 / 2 + 1 by ring, Real.rpow_add hT, Real.rpow_add hT,
      Real.rpow_one]
  rw [aZero_eq_azInt]
  calc ‖-(1 / 2 : ℂ) * ell * ∫ t in Ioi (0 : ℝ), azInt lam μ (Bmat ν μ χf A) t‖
      ≤ ‖-(1 / 2 : ℂ) * ell‖ * ‖∫ t in Ioi (0 : ℝ), azInt lam μ (Bmat ν μ χf A) t‖ :=
        norm_mul_le _ _
    _ ≤ ‖-(1 / 2 : ℂ) * ell‖ * (((11 / 10 : ℝ) / ν) * azK lam μ ν χf A) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (1 / 2 * ‖ell‖) * (((11 / 10 : ℝ) / ν) * azK lam μ ν χf A) := by rw [hn]
    _ = (‖ell‖ * (1 + μ) * ((11 / 10 : ℝ) / ν) ^ (μ + 5 / 2) *
          Real.exp (|lam.re| * ((11 / 10 : ℝ) / ν))) * affM ν χf A := by
        unfold azK
        rw [hpow]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
