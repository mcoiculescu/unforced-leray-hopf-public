import UnforcedLeray.Analysis.Sturm.GlobalH1Cutoff

/-!
# Strong H¹ errors of the actual whole-line cutoffs

Both squared L² errors tend to zero for the explicit cutoff approximation.
The bounds are integrable functions of the given field and derivative; this
is genuine strong approximation, with no assumed approximation premise.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace UnforcedLeray.Sturm.GlobalH1CutoffErrors
open GaussianCompactTrial GlobalH1Cutoff

/-- The value error has a fixed integrable square majorant. -/
theorem value_error_square_le (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    (approximation f n t - f t) ^ 2 ≤ 4 * f t ^ 2 := by
  have h := approximation_square_le f n t
  nlinarith [sq_nonneg (approximation f n t + f t)]

/-- The derivative error has a fixed integrable square majorant. -/
theorem deriv_error_square_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M) (n : ℕ) (t : ℝ) :
    (deriv (approximation f n) t - deriv f t) ^ 2 ≤
      4 * M ^ 2 * f t ^ 2 + 6 * deriv f t ^ 2 := by
  have h := deriv_approximation_square_le hf M hM hbound n t
  nlinarith [sq_nonneg (deriv (approximation f n) t + deriv f t)]

theorem integrable_value_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 volume) (n : ℕ) :
    Integrable (fun t => (approximation f n t - f t) ^ 2) :=
  ((approximation_memLp_two hf n).sub hf2).integrable_sq

theorem integrable_deriv_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hdf2 : MemLp (deriv f) 2 volume) (n : ℕ) :
    Integrable (fun t => (deriv (approximation f n) t - deriv f t) ^ 2) :=
  ((deriv_approximation_memLp_two hf n).sub hdf2).integrable_sq

/-- The actual cutoff values converge strongly in squared L² norm. -/
theorem integral_value_error_tendsto_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 volume) :
    Tendsto (fun n => ∫ t, (approximation f n t - f t) ^ 2) atTop (𝓝 (0 : ℝ)) := by
  have hlim : Tendsto (fun n => ∫ t, (approximation f n t - f t) ^ 2) atTop
      (𝓝 (∫ _t : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun t => 4 * f t ^ 2)
      (fun n => (((approximation_contDiff hf n).continuous.sub hf.continuous).pow 2).aestronglyMeasurable)
      (hf2.integrable_sq.const_mul 4)
    · intro n
      filter_upwards [] with t
      simpa only [Real.norm_eq_abs, Pi.pow_apply, Pi.sub_apply, abs_sq] using value_error_square_le f n t
    · filter_upwards [] with t
      simpa [Pi.pow_apply, Pi.sub_apply] using ((approximation_tendsto f t).sub_const (f t)).pow 2
  simpa only [integral_zero] using hlim

/-- The actual cutoff derivatives converge strongly in squared L² norm. -/
theorem integral_deriv_error_tendsto_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 volume) (hdf2 : MemLp (deriv f) 2 volume) :
    Tendsto (fun n => ∫ t, (deriv (approximation f n) t - deriv f t) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨M, hM, hbound⟩ := exists_bump_derivative_bound
  have hlim : Tendsto (fun n => ∫ t, (deriv (approximation f n) t - deriv f t) ^ 2)
      atTop (𝓝 (∫ _t : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun t => 4 * M ^ 2 * f t ^ 2 + 6 * deriv f t ^ 2)
      (fun n => (((approximation_contDiff hf n).continuous_deriv_one.sub
        hf.continuous_deriv_one).pow 2).aestronglyMeasurable)
      ((hf2.integrable_sq.const_mul (4 * M ^ 2)).add (hdf2.integrable_sq.const_mul 6))
    · intro n
      filter_upwards [] with t
      simpa only [Real.norm_eq_abs, Pi.pow_apply, Pi.sub_apply, abs_sq] using deriv_error_square_le hf M hM hbound n t
    · filter_upwards [] with t
      simpa [Pi.pow_apply, Pi.sub_apply] using
        ((deriv_approximation_tendsto hf t).sub_const (deriv f t)).pow 2
  simpa only [integral_zero] using hlim

end UnforcedLeray.Sturm.GlobalH1CutoffErrors
