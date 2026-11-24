import UnforcedLeray.Analysis.Sturm.GlobalH1Cutoff

/-!
# Actual compact approximation through the second derivative

The second derivative of `χ(t/(n+1)) f(t)` is computed explicitly. Bounds on
the first two derivatives of the fixed compact bump give an integrable
majorant, so the squared L² error of the second derivative tends to zero.
This is an actual cutoff construction for classical H² functions.
-/

noncomputable section
namespace UnforcedLeray.Sturm.GlobalH2Cutoff
open MeasureTheory Set Filter
open scoped Topology ContDiff
open GaussianCompactTrial GlobalH1Cutoff

/-- C² regularity is preserved by the explicit cutoff. -/
theorem approximation_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (n : ℕ) :
    ContDiff ℝ 2 (approximation f n) :=
  (bump.contDiff.comp (contDiff_id.div_const (scale n))).mul hf

theorem continuous_second_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (deriv (deriv f)) := by
  have hdf : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact hdf.continuous_deriv_one

/-- The literal second-derivative coefficient of the dilated cutoff. -/
def secondCutoffCoefficient (n : ℕ) (t : ℝ) : ℝ :=
  deriv (deriv (bump : ℝ → ℝ)) (t / scale n) / (scale n) ^ 2

theorem hasDerivAt_cutoff_derivative_coefficient (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x => deriv (bump : ℝ → ℝ) (x / scale n) / scale n)
      (secondCutoffCoefficient n t) t := by
  have hb : ContDiff ℝ 2 (bump : ℝ → ℝ) := bump.contDiff
  have h := ((hb.differentiable_deriv_two (t / scale n)).hasDerivAt.comp t
    ((hasDerivAt_id t).div_const (scale n))).div_const (scale n)
  convert h using 1 <;> first | rfl | (simp [secondCutoffCoefficient, div_eq_mul_inv]; ring)

/-- Full product rule, including both cross terms and the second cutoff derivative. -/
theorem second_deriv_approximation {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (n : ℕ) (t : ℝ) :
    deriv (deriv (approximation f n)) t =
      secondCutoffCoefficient n t * f t +
        2 * (deriv (bump : ℝ → ℝ) (t / scale n) / scale n) * deriv f t +
          cutoff n t * deriv (deriv f) t := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hdf : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have he : deriv (approximation f n) = fun x =>
      deriv (bump : ℝ → ℝ) (x / scale n) / scale n * f x +
        cutoff n x * deriv f x := funext (deriv_approximation hf1 n)
  rw [he]
  have h := ((hasDerivAt_cutoff_derivative_coefficient n t).mul
    ((hf1.differentiable (by norm_num) t).hasDerivAt)).add
      ((hasDerivAt_cutoff n t).mul ((hdf.differentiable (by norm_num) t).hasDerivAt))
  change deriv ((fun x => deriv (bump : ℝ → ℝ) (x / scale n) / scale n) * f +
    cutoff n * deriv f) t = _
  rw [h.deriv]
  ring

/-- A finite global bound for the actual second derivative of the fixed bump. -/
theorem exists_bump_second_derivative_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv (deriv (bump : ℝ → ℝ)) t| ≤ M := by
  have hb : ContDiff ℝ 2 (bump : ℝ → ℝ) := bump.contDiff
  obtain ⟨C, hC⟩ := (continuous_second_deriv hb).bounded_above_of_compact_support
    bump.hasCompactSupport.deriv.deriv
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro t
  have h := hC t
  rw [Real.norm_eq_abs] at h
  linarith [le_abs_self C]

theorem secondCutoffCoefficient_bound (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |deriv (deriv (bump : ℝ → ℝ)) t| ≤ M) (n : ℕ) (t : ℝ) :
    |secondCutoffCoefficient n t| ≤ M := by
  unfold secondCutoffCoefficient
  rw [abs_div, abs_sq]
  apply (div_le_iff₀ (sq_pos_of_pos (scale_pos n))).2
  have hb := hbound (t / scale n)
  have hs := one_le_scale n
  have hsq : 1 ≤ (scale n) ^ 2 := by nlinarith
  nlinarith

theorem second_deriv_approximation_abs_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hbound₁ : ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M₁)
    (hbound₂ : ∀ t : ℝ, |deriv (deriv (bump : ℝ → ℝ)) t| ≤ M₂) (n : ℕ) (t : ℝ) :
    |deriv (deriv (approximation f n)) t| ≤
      M₂ * |f t| + 2 * M₁ * |deriv f t| + |deriv (deriv f) t| := by
  rw [second_deriv_approximation hf]
  calc
    |secondCutoffCoefficient n t * f t +
        2 * (deriv (bump : ℝ → ℝ) (t / scale n) / scale n) * deriv f t +
          cutoff n t * deriv (deriv f) t| ≤
        |secondCutoffCoefficient n t * f t| +
          |2 * (deriv (bump : ℝ → ℝ) (t / scale n) / scale n) * deriv f t| +
            |cutoff n t * deriv (deriv f) t| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |secondCutoffCoefficient n t| * |f t| +
        2 * |deriv (bump : ℝ → ℝ) (t / scale n) / scale n| * |deriv f t| +
          cutoff n t * |deriv (deriv f) t| := by
      simp only [abs_mul, abs_of_nonneg (cutoff_bounds n t).1,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ M₂ * |f t| + 2 * M₁ * |deriv f t| + |deriv (deriv f) t| := by
      gcongr
      · exact secondCutoffCoefficient_bound M₂ hM₂ hbound₂ n t
      · exact cutoff_derivative_bound M₁ hM₁ hbound₁ n t
      · exact mul_le_of_le_one_left (abs_nonneg _) (cutoff_bounds n t).2

theorem second_deriv_approximation_square_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hbound₁ : ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M₁)
    (hbound₂ : ∀ t : ℝ, |deriv (deriv (bump : ℝ → ℝ)) t| ≤ M₂) (n : ℕ) (t : ℝ) :
    deriv (deriv (approximation f n)) t ^ 2 ≤
      3 * M₂ ^ 2 * f t ^ 2 + 12 * M₁ ^ 2 * deriv f t ^ 2 +
        3 * deriv (deriv f) t ^ 2 := by
  have hpos : 0 ≤ M₂ * |f t| + 2 * M₁ * |deriv f t| + |deriv (deriv f) t| := by positivity
  have h := (sq_le_sq₀ (abs_nonneg _) hpos).2
    (second_deriv_approximation_abs_le hf M₁ M₂ hM₁ hM₂ hbound₁ hbound₂ n t)
  simp only [sq_abs] at h
  have hab := sq_nonneg (M₂ * |f t| - 2 * M₁ * |deriv f t|)
  have hac := sq_nonneg (M₂ * |f t| - |deriv (deriv f) t|)
  have hbc := sq_nonneg (2 * M₁ * |deriv f t| - |deriv (deriv f) t|)
  nlinarith [sq_abs (f t), sq_abs (deriv f t), sq_abs (deriv (deriv f) t)]

theorem secondCutoffCoefficient_tendsto_zero (t : ℝ) :
    Tendsto (fun n => secondCutoffCoefficient n t) atTop (𝓝 (0 : ℝ)) := by
  have hb : ContDiff ℝ 2 (bump : ℝ → ℝ) := bump.contDiff
  have h := (continuous_second_deriv hb).continuousAt.tendsto.comp (tendsto_div_scale t)
  simpa [secondCutoffCoefficient, div_pow, div_eq_mul_inv, one_div, Function.comp_def] using
    h.mul (tendsto_inv_scale.pow 2)

theorem second_deriv_approximation_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) :
    Tendsto (fun n => deriv (deriv (approximation f n)) t) atTop
      (𝓝 (deriv (deriv f) t)) := by
  simp_rw [second_deriv_approximation hf]
  simpa only [zero_mul, one_mul, zero_add, mul_zero] using
    (((secondCutoffCoefficient_tendsto_zero t).mul_const (f t)).add
      (((cutoff_derivative_tendsto_zero t).const_mul 2).mul_const (deriv f t))).add
      ((cutoff_tendsto_one t).mul_const (deriv (deriv f) t))

theorem second_deriv_approximation_memLp_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (n : ℕ) :
    MemLp (deriv (deriv (approximation f n))) 2 volume :=
  (continuous_second_deriv (approximation_contDiff_two hf n)).memLp_of_hasCompactSupport
    (approximation_hasCompactSupport f n).deriv.deriv

/-- Every approximating error is square integrable, independent of the limit argument. -/
theorem integrable_second_error {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hddf : MemLp (deriv (deriv f)) 2 volume) (n : ℕ) :
    Integrable (fun t => (deriv (deriv (approximation f n)) t - deriv (deriv f) t) ^ 2) :=
  ((second_deriv_approximation_memLp_two hf n).sub hddf).integrable_sq

/-- Squared-L² convergence of the actual second derivative, from explicit cutoffs. -/
theorem integral_second_error_tendsto_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hf2 : MemLp f 2 volume) (hdf2 : MemLp (deriv f) 2 volume)
    (hddf2 : MemLp (deriv (deriv f)) 2 volume) :
    Tendsto (fun n => ∫ t,
      (deriv (deriv (approximation f n)) t - deriv (deriv f) t) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨M₁, hM₁, hbound₁⟩ := exists_bump_derivative_bound
  obtain ⟨M₂, hM₂, hbound₂⟩ := exists_bump_second_derivative_bound
  let majorant : ℝ → ℝ := fun t =>
    6 * M₂ ^ 2 * f t ^ 2 + 24 * M₁ ^ 2 * deriv f t ^ 2 +
      8 * deriv (deriv f) t ^ 2
  have hi : Integrable majorant :=
    ((hf2.integrable_sq.const_mul (6 * M₂ ^ 2)).add
      (hdf2.integrable_sq.const_mul (24 * M₁ ^ 2))).add
        (hddf2.integrable_sq.const_mul 8)
  have hlim : Tendsto (fun n => ∫ t,
      (deriv (deriv (approximation f n)) t - deriv (deriv f) t) ^ 2)
      atTop (𝓝 (∫ _ : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence majorant
      (fun n => (((continuous_second_deriv (approximation_contDiff_two hf n)).sub
        (continuous_second_deriv hf)).pow 2).aestronglyMeasurable) hi
    · intro n
      filter_upwards [] with t
      simp only [Real.norm_eq_abs, Pi.pow_apply, Pi.sub_apply, abs_sq]
      have h := second_deriv_approximation_square_le hf M₁ M₂ hM₁ hM₂ hbound₁ hbound₂ n t
      dsimp [majorant]
      nlinarith [sq_nonneg (deriv (deriv (approximation f n)) t + deriv (deriv f) t)]
    · filter_upwards [] with t
      simpa only [Pi.pow_apply, Pi.sub_apply, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        ((second_deriv_approximation_tendsto hf t).sub_const (deriv (deriv f) t)).pow 2
  simpa only [integral_zero] using hlim

end UnforcedLeray.Sturm.GlobalH2Cutoff
