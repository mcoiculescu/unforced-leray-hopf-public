import UnforcedLeray.GaussianCompactTrial
import UnforcedLeray.Analysis.Sturm.QuadraticForm

/-!
# Genuine compact approximation of classical H¹ functions on the line

The cutoff is the actual smooth bump `χ(t/(n+1))`, with its derivative computed
by the chain rule. Its compact approximations preserve any prescribed zero of
the function. Dominated convergence proves convergence of the full quadratic
energy for every bounded measurable potential; no approximation or density
premise is introduced.
-/

noncomputable section
namespace UnforcedLeray.Sturm.GlobalH1Cutoff
open MeasureTheory Set Filter
open scoped Topology ContDiff
open GaussianCompactTrial

/-- The actual compact cutoff approximation of a real function. -/
def approximation (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ := cutoff n t * f t

theorem approximation_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    ContDiff ℝ 1 (approximation f n) := (cutoff_contDiff n).mul hf

theorem approximation_contDiff_infty {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (approximation f n) :=
  (bump.contDiff.comp (contDiff_id.div_const (scale n))).mul hf

theorem approximation_support_subset (f : ℝ → ℝ) (n : ℕ) :
    Function.support (approximation f n) ⊆ Icc (-2 * scale n) (2 * scale n) := by
  intro t ht
  have hcut : cutoff n t ≠ 0 := by
    intro hz
    apply ht
    simp [approximation, hz]
  have hmem : t / scale n ∈ Metric.ball 0 (2 : ℝ) := by
    rw [← show bump.rOut = (2 : ℝ) from rfl, ← bump.support_eq]
    exact hcut
  have habs : |t / scale n| < 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hmem
  rw [abs_div, abs_of_pos (scale_pos n)] at habs
  have htbound : |t| < 2 * scale n := (div_lt_iff₀ (scale_pos n)).mp habs
  obtain ⟨hl, hu⟩ := abs_lt.mp htbound
  exact ⟨by linarith, hu.le⟩

theorem approximation_hasCompactSupport (f : ℝ → ℝ) (n : ℕ) :
    HasCompactSupport (approximation f n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (approximation_support_subset f n)

/-- Multiplication by this cutoff preserves the exact zero trace at any point. -/
theorem approximation_zero_at {f : ℝ → ℝ} {a : ℝ} (ha : f a = 0) (n : ℕ) :
    approximation f n a = 0 := by simp [approximation, ha]

theorem deriv_approximation {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) (t : ℝ) :
    deriv (approximation f n) t =
      deriv (bump : ℝ → ℝ) (t / scale n) / scale n * f t +
        cutoff n t * deriv f t :=
  ((hasDerivAt_cutoff n t).mul ((hf.differentiable (by norm_num) t).hasDerivAt)).deriv

theorem approximation_memLp_two {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    MemLp (approximation f n) 2 volume :=
  (approximation_contDiff hf n).continuous.memLp_of_hasCompactSupport
    (approximation_hasCompactSupport f n)

theorem deriv_approximation_memLp_two {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    MemLp (deriv (approximation f n)) 2 volume :=
  (approximation_contDiff hf n).continuous_deriv_one.memLp_of_hasCompactSupport
    (approximation_hasCompactSupport f n).deriv

theorem approximation_abs_le (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    |approximation f n t| ≤ |f t| := by
  unfold approximation
  rw [abs_mul, abs_of_nonneg (cutoff_bounds n t).1]
  exact mul_le_of_le_one_left (abs_nonneg _) (cutoff_bounds n t).2

theorem approximation_square_le (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    approximation f n t ^ 2 ≤ f t ^ 2 := by
  have h := (sq_le_sq₀ (abs_nonneg (approximation f n t)) (abs_nonneg (f t))).2
    (approximation_abs_le f n t)
  simpa only [sq_abs] using h

theorem deriv_approximation_abs_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M) (n : ℕ) (t : ℝ) :
    |deriv (approximation f n) t| ≤ M * |f t| + |deriv f t| := by
  rw [deriv_approximation hf]
  calc
    |deriv (bump : ℝ → ℝ) (t / scale n) / scale n * f t +
        cutoff n t * deriv f t| ≤
        |deriv (bump : ℝ → ℝ) (t / scale n) / scale n * f t| +
          |cutoff n t * deriv f t| := abs_add_le _ _
    _ = |deriv (bump : ℝ → ℝ) (t / scale n) / scale n| * |f t| +
          cutoff n t * |deriv f t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_bounds n t).1]
    _ ≤ M * |f t| + |deriv f t| :=
      add_le_add (mul_le_mul_of_nonneg_right (cutoff_derivative_bound M hM hbound n t)
        (abs_nonneg _))
        (mul_le_of_le_one_left (abs_nonneg _) (cutoff_bounds n t).2)

theorem deriv_approximation_square_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M) (n : ℕ) (t : ℝ) :
    deriv (approximation f n) t ^ 2 ≤ 2 * M ^ 2 * f t ^ 2 + 2 * deriv f t ^ 2 := by
  have hpos : 0 ≤ M * |f t| + |deriv f t| := by positivity
  have h := (sq_le_sq₀ (abs_nonneg (deriv (approximation f n) t)) hpos).2
    (deriv_approximation_abs_le hf M hM hbound n t)
  have hs := sq_nonneg (M * |f t| - |deriv f t|)
  simp only [sq_abs] at h
  nlinarith [sq_abs (f t), sq_abs (deriv f t)]

theorem approximation_tendsto (f : ℝ → ℝ) (t : ℝ) :
    Tendsto (fun n => approximation f n t) atTop (𝓝 (f t)) := by
  simpa only [approximation, one_mul] using (cutoff_tendsto_one t).mul_const (f t)

theorem deriv_approximation_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    Tendsto (fun n => deriv (approximation f n) t) atTop (𝓝 (deriv f t)) := by
  simp_rw [deriv_approximation hf]
  simpa only [zero_mul, one_mul, zero_add] using
    ((cutoff_derivative_tendsto_zero t).mul_const (f t)).add
      ((cutoff_tendsto_one t).mul_const (deriv f t))

/-- The real quadratic integrand for an arbitrary potential. -/
def formIntegrand (V f : ℝ → ℝ) (t : ℝ) : ℝ := deriv f t ^ 2 + V t * f t ^ 2

def formMajorant (f : ℝ → ℝ) (M B t : ℝ) : ℝ :=
  2 * deriv f t ^ 2 + (2 * M ^ 2 + B) * f t ^ 2

theorem integrable_formMajorant {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hdf : MemLp (deriv f) 2 volume) (M B : ℝ) : Integrable (formMajorant f M B) :=
  (hdf.integrable_sq.const_mul 2).add (hf.integrable_sq.const_mul (2 * M ^ 2 + B))

theorem measurable_formIntegrand {f V : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hV : Measurable V) : Measurable (formIntegrand V f) :=
  (hf.continuous_deriv_one.measurable.pow_const 2).add
    (hV.mul (hf.continuous.measurable.pow_const 2))

theorem approximation_form_bound {f V : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {B : ℝ} (hB : 0 ≤ B) (hV : ∀ t, |V t| ≤ B)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M) (n : ℕ) (t : ℝ) :
    ‖formIntegrand V (approximation f n) t‖ ≤ formMajorant f M B t := by
  unfold formIntegrand formMajorant
  rw [Real.norm_eq_abs]
  calc
    |deriv (approximation f n) t ^ 2 + V t * approximation f n t ^ 2| ≤
        |deriv (approximation f n) t ^ 2| + |V t * approximation f n t ^ 2| := abs_add_le _ _
    _ = deriv (approximation f n) t ^ 2 + |V t| * approximation f n t ^ 2 := by
      simp only [abs_mul, abs_sq]
    _ ≤ deriv (approximation f n) t ^ 2 + B * approximation f n t ^ 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (hV t) (sq_nonneg _))
    _ ≤ 2 * deriv f t ^ 2 + (2 * M ^ 2 + B) * f t ^ 2 := by
      have hd := deriv_approximation_square_le hf M hM hbound n t
      have hv := mul_le_mul_of_nonneg_left (approximation_square_le f n t) hB
      nlinarith

theorem formIntegrand_approximation_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (V : ℝ → ℝ) (t : ℝ) :
    Tendsto (fun n => formIntegrand V (approximation f n) t) atTop
      (𝓝 (formIntegrand V f t)) :=
  ((deriv_approximation_tendsto hf t).pow 2).add
    (((approximation_tendsto f t).pow 2).const_mul (V t))

/-- Each original and approximating quadratic form is an actual finite integral. -/
theorem integrable_formIntegrand {f V : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hdf : MemLp (deriv f) 2 volume)
    (hV : Measurable V) {B : ℝ} (hbound : ∀ t, |V t| ≤ B) :
    Integrable (formIntegrand V f) := by
  apply hdf.integrable_sq.add
  exact hf.integrable_sq.bdd_mul hV.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hbound t))

/-- Actual dominated convergence of the complete derivative-plus-potential energy. -/
theorem integral_form_tendsto {f V : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 volume) (hdf2 : MemLp (deriv f) 2 volume)
    (hV : Measurable V) {B : ℝ} (hB : 0 ≤ B) (hVbound : ∀ t, |V t| ≤ B) :
    Tendsto (fun n => ∫ t, formIntegrand V (approximation f n) t) atTop
      (𝓝 (∫ t, formIntegrand V f t)) := by
  obtain ⟨M, hM, hbound⟩ := exists_bump_derivative_bound
  apply tendsto_integral_of_dominated_convergence (formMajorant f M B)
    (fun n => (measurable_formIntegrand (approximation_contDiff hf n) hV).aestronglyMeasurable)
    (integrable_formMajorant hf2 hdf2 M B)
  · intro n
    filter_upwards [] with t
    exact approximation_form_bound hf hB hVbound M hM hbound n t
  · filter_upwards [] with t
    exact formIntegrand_approximation_tendsto hf V t

end UnforcedLeray.Sturm.GlobalH1Cutoff
