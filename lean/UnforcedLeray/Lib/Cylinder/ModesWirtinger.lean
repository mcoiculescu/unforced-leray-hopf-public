import UnforcedLeray.Lib.Cylinder.Modes

/-!
# `q`-averages: Cauchy-Schwarz and the Wirtinger inequality on a slice (INF13, CY04)


§5 CY04 (`eLpNorm_qAvg_le` at `p = 2`, `norm_sub_qAvg_le`), in slice form: at each height `η`.

* `norm_sq_qAvg_le`: `|f̄(η)|² ≤ c⁻¹ ∫_{-c/2}^{c/2} |f(q, η)|² dq`;
* `wirtinger_slice`: for a `C¹`, `c`-periodic `f`,
  `∫_{-c/2}^{c/2} |f(q,η) - f̄(η)|² dq ≤ (c/2π)² ∫_{-c/2}^{c/2} |∂_q f(q,η)|² dq`.
Both follow from Parseval on the slice and `qMode_partialQ`.  The cell forms (integrating in
`η`) are not built here.

`paper/main.tex` lines 9077-9085 (B0566): the oscillatory part `F_⊥` is the zero-mean part;
the constant `c/(2π)` is the sharp constant of `‖J_q‖`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Complex
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Cyl

theorem memLp_slice_of_continuous {c : ℝ} {f : Plane → ℂ} (hf : Continuous f) (η : ℝ) :
    MemLp (fun q => f (q, η)) 2 (volume.restrict (Ioc (-c / 2) (c / 2))) := by
  have hcont : Continuous fun q : ℝ => f (q, η) := hf.comp (continuous_id.prodMk continuous_const)
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  exact ((hcont.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
    Ioc_subset_Icc_self

/-- `|f̄(η)|² ≤ c⁻¹ ∫_{-c/2}^{c/2} |f(q,η)|² dq` (Cauchy-Schwarz through Parseval). -/
theorem norm_sq_qAvg_le {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (η : ℝ)
    (hL2 : MemLp (fun q => f (q, η)) 2 (volume.restrict (Ioc (-c / 2) (c / 2)))) :
    ‖qAvg c f η‖ ^ 2 ≤ c⁻¹ * ∫ q in (-c / 2)..(c / 2), ‖f (q, η)‖ ^ 2 := by
  have h := hasSum_sq_qMode hc η hL2
  rw [← qMode_zero hc]
  exact le_hasSum h 0 fun j _ => by positivity

/-- Parseval form of Wirtinger's inequality on a slice:
`c⁻¹ ∫|f|² - |f̄|² ≤ (c/2π)² c⁻¹ ∫|∂_q f|²`. -/
theorem wirtinger_slice_variance {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : IsPeriodic c f) (η : ℝ) :
    c⁻¹ * (∫ q in (-c / 2)..(c / 2), ‖f (q, η)‖ ^ 2) - ‖qAvg c f η‖ ^ 2 ≤
      (c / (2 * π)) ^ 2 * (c⁻¹ * ∫ q in (-c / 2)..(c / 2), ‖partialQ f (q, η)‖ ^ 2) := by
  have hF := hasSum_sq_qMode hc η (memLp_slice_of_continuous hf.continuous η)
  have hD := hasSum_sq_qMode hc η
    (memLp_slice_of_continuous (C1_partial_of_contDiff hf).1 η)
  have hU := hF.update 0 0
  rw [qMode_zero hc] at hU
  refine hasSum_le (fun n => ?_) (by simpa [sub_eq_add_neg, add_comm] using hU)
    (hD.mul_left ((c / (2 * π)) ^ 2))
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Function.update_self]; positivity
  · rw [Function.update_of_ne hn, qMode_partialQ hc hf hper hn, norm_mul, mul_pow]
    have hk : ‖(2 * π * I * n / c : ℂ)‖ = 2 * π * |(n : ℝ)| / c := by
      rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
        Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, abs_of_pos hc, mul_one]
      norm_num
    rw [hk]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    have hpos : 0 < 2 * π / c := by positivity
    have : (c / (2 * π)) ^ 2 * (2 * π * |(n : ℝ)| / c) ^ 2 = |(n : ℝ)| ^ 2 := by
      field_simp
    calc ‖qMode c hc n f η‖ ^ 2 ≤ |(n : ℝ)| ^ 2 * ‖qMode c hc n f η‖ ^ 2 := by
          have : (1 : ℝ) ≤ |(n : ℝ)| ^ 2 := by nlinarith
          nlinarith [sq_nonneg ‖qMode c hc n f η‖]
      _ = (c / (2 * π)) ^ 2 * ((2 * π * |(n : ℝ)| / c) ^ 2 * ‖qMode c hc n f η‖ ^ 2) := by
          rw [← this]; ring

/-- `∫_{-c/2}^{c/2} |f - f̄|² = ∫_{-c/2}^{c/2} |f|² - c |f̄|²` for a continuous slice. -/
theorem integral_norm_sub_qAvg_sq {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (hf : Continuous f)
    (η : ℝ) :
    ∫ q in (-c / 2)..(c / 2), ‖f (q, η) - qAvg c f η‖ ^ 2 =
      (∫ q in (-c / 2)..(c / 2), ‖f (q, η)‖ ^ 2) - c * ‖qAvg c f η‖ ^ 2 := by
  set k := qAvg c f η
  have hcont : Continuous fun q : ℝ => f (q, η) := hf.comp (continuous_id.prodMk continuous_const)
  have hle : -c / 2 ≤ c / 2 := by linarith
  have hint : ∫ q in (-c / 2)..(c / 2), f (q, η) = c * k := by
    simp only [k, qAvg]
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo,
      ← integral_Ico_eq_integral_Ioo, ← mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hc.ne'), one_mul]
  have hpt : ∀ q, ‖f (q, η) - k‖ ^ 2 =
      ‖f (q, η)‖ ^ 2 + ‖k‖ ^ 2 - 2 * (f (q, η) * conj k).re := by
    intro q
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  simp_rw [hpt]
  have i1 : IntervalIntegrable (fun q => ‖f (q, η)‖ ^ 2) volume (-c / 2) (c / 2) :=
    (hcont.norm.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun q => (f (q, η) * conj k).re) volume (-c / 2) (c / 2) :=
    (Complex.continuous_re.comp (hcont.mul continuous_const)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (i1.add intervalIntegrable_const) (i2.const_mul 2),
    intervalIntegral.integral_add i1 intervalIntegrable_const, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  have hre : ∫ q in (-c / 2)..(c / 2), (f (q, η) * conj k).re = c * ‖k‖ ^ 2 := by
    have h := intervalIntegral.intervalIntegral_re (μ := volume) (a := -c / 2) (b := c / 2)
      (f := fun q => f (q, η) * conj k) ((hcont.mul continuous_const).intervalIntegrable _ _)
    simp only [RCLike.re_to_complex] at h
    rw [h, intervalIntegral.integral_mul_const, hint, mul_assoc, Complex.mul_conj,
      Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [hre, smul_eq_mul]
  ring

/-- **Wirtinger's inequality on a slice** (CY04 `norm_sub_qAvg_le`, slice form): for a `C¹`,
`c`-periodic `f`, `∫_{-c/2}^{c/2} |f(q,η) - f̄(η)|² dq ≤ (c/2π)² ∫_{-c/2}^{c/2} |∂_q f(q,η)|² dq`. -/
theorem wirtinger_slice {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : IsPeriodic c f) (η : ℝ) :
    ∫ q in (-c / 2)..(c / 2), ‖f (q, η) - qAvg c f η‖ ^ 2 ≤
      (c / (2 * π)) ^ 2 * ∫ q in (-c / 2)..(c / 2), ‖partialQ f (q, η)‖ ^ 2 := by
  rw [integral_norm_sub_qAvg_sq hc hf.continuous]
  have h := wirtinger_slice_variance hc hf hper η
  have hc' : 0 < c := hc
  have := mul_le_mul_of_nonneg_left h hc'.le
  rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
  calc _ ≤ c * ((c / (2 * π)) ^ 2 * (c⁻¹ * ∫ q in (-c / 2)..(c / 2),
        ‖partialQ f (q, η)‖ ^ 2)) := this
    _ = _ := by field_simp

end UnforcedLeray.Cyl
