import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_3

/-!
# `PartII-a:N01/9/1/3/3/2/1/3/1`: `HardyBetaFinite`

Source `the November 2 reference manuscript`
lines 3541-3552.  The integrand is `t^(a-3/4) (1-t)^(-1/2)` on `(0,1)`, which is the complex
Beta integrand with parameters `u = a + 1/4`, `v = 1/2`, both of positive real part.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

theorem hardyBetaFinite : UnforcedLeray.Short.PartIIa.N01.HardyBetaFinite := by
  intro a ha
  set u : ℂ := ((a + 1 / 4 : ℝ) : ℂ) with hu_def
  set v : ℂ := ((1 / 2 : ℝ) : ℂ) with hv_def
  have hu : 0 < u.re := by
    rw [hu_def, Complex.ofReal_re]; linarith
  have hv : 0 < v.re := by
    rw [hv_def, Complex.ofReal_re]; norm_num
  have hI := Complex.betaIntegral_convergent hu hv
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hI
  have hfin : ∫⁻ t in Ioo (0:ℝ) 1, ‖(t:ℂ) ^ (u - 1) * (1 - (t:ℂ)) ^ (v - 1)‖ₑ < ∞ :=
    (hI.mono_set Ioo_subset_Ioc_self).2
  refine lt_of_eq_of_lt (setLIntegral_congr_fun measurableSet_Ioo ?_) hfin
  intro t ht
  dsimp only
  have h0 : 0 < t := ht.1
  have h1 : 0 < 1 - t := by linarith [ht.2]
  have hre1 : (u - 1).re = a - 3 / 4 := by
    rw [hu_def, Complex.sub_re, Complex.ofReal_re, Complex.one_re]; ring
  have hre2 : (v - 1).re = -(1 / 2) := by
    rw [hv_def, Complex.sub_re, Complex.ofReal_re, Complex.one_re]; ring
  have e : (1 - (t:ℂ)) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
  have hp : t ^ (a - 1) * t ^ (1 / 4 : ℝ) = t ^ (a - 3 / 4) := by
    rw [← Real.rpow_add h0]; congr 1; ring
  rw [e, ← ofReal_norm, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h0,
    Complex.norm_cpow_eq_rpow_re_of_pos h1, hre1, hre2,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg h0.le _) (Real.rpow_nonneg h1.le _)),
    mul_right_comm, hp]

end UnforcedLeray.Short.PartIIa.N01
