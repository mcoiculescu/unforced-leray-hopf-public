import UnforcedLeray.GaussianLogTrial
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Compact negative trials by an actual smooth cutoff

We construct a fixed smooth bump and dilate it by `n+1`. Dominated convergence
of the actual quadratic integrands preserves the strictly negative Gaussian
trial form. Compact approximation and negative-test existence are conclusions,
not assumptions.
-/

noncomputable section

namespace UnforcedLeray.GaussianCompactTrial

open MeasureTheory Set Filter GaussianTrial GaussianQuadratic GaussianLogTrial
open scoped Topology ContDiff

/-- Fixed smooth cutoff equal to one on `[-1,1]`, zero outside `[-2,2]`. -/
def bump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def scale (n : ℕ) : ℝ := n + 1

def cutoff (n : ℕ) (t : ℝ) : ℝ := bump (t / scale n)

def compactTrial (n : ℕ) (t : ℝ) : ℝ := cutoff n t * logTrial t

theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

theorem one_le_scale (n : ℕ) : 1 ≤ scale n := by
  unfold scale
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem bump_at_zero : bump 0 = 1 := by
  apply bump.one_of_mem_closedBall
  simp [bump]

theorem cutoff_bounds (n : ℕ) (t : ℝ) : 0 ≤ cutoff n t ∧ cutoff n t ≤ 1 :=
  ⟨bump.nonneg, bump.le_one⟩

theorem cutoff_contDiff (n : ℕ) : ContDiff ℝ 1 (cutoff n) :=
  bump.contDiff.comp (contDiff_id.div_const (scale n))

theorem compactTrial_contDiff (n : ℕ) : ContDiff ℝ 1 (compactTrial n) := by
  apply (cutoff_contDiff n).mul
  unfold logTrial radialTrial
  fun_prop

/-- The constructed trials are in fact infinitely differentiable. -/
theorem compactTrial_contDiff_infty (n : ℕ) : ContDiff ℝ ∞ (compactTrial n) := by
  apply (bump.contDiff.comp (contDiff_id.div_const (scale n))).mul
  unfold logTrial radialTrial
  fun_prop

theorem hasDerivAt_cutoff (n : ℕ) (t : ℝ) :
    HasDerivAt (cutoff n) (deriv (bump : ℝ → ℝ) (t / scale n) / scale n) t := by
  have hb : ContDiff ℝ 1 (bump : ℝ → ℝ) := bump.contDiff
  convert ((hb.differentiable (by norm_num) (t / scale n)).hasDerivAt).comp t
    ((hasDerivAt_id t).div_const (scale n)) using 1 <;>
    first | rfl | (simp [div_eq_mul_inv])

theorem deriv_compactTrial (n : ℕ) (t : ℝ) :
    deriv (compactTrial n) t =
      deriv (bump : ℝ → ℝ) (t / scale n) / scale n * logTrial t +
        cutoff n t * deriv logTrial t :=
  ((hasDerivAt_cutoff n t).mul
    (hasDerivAt_logTrial t).differentiableAt.hasDerivAt).deriv

theorem compactTrial_support_subset (n : ℕ) :
    Function.support (compactTrial n) ⊆ Icc (-2 * scale n) (2 * scale n) := by
  intro t ht
  have hcut : cutoff n t ≠ 0 := by
    intro h
    apply ht
    simp [compactTrial, h]
  have hmem : t / scale n ∈ Metric.ball 0 (2 : ℝ) := by
    rw [← show bump.rOut = (2 : ℝ) from rfl, ← bump.support_eq]
    exact hcut
  have habs : |t / scale n| < 2 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hmem
  rw [abs_div, abs_of_pos (scale_pos n)] at habs
  have htbound : |t| < 2 * scale n := (div_lt_iff₀ (scale_pos n)).mp habs
  obtain ⟨hl, hu⟩ := abs_lt.mp htbound
  exact ⟨by linarith, hu.le⟩

theorem compactTrial_hasCompactSupport (n : ℕ) : HasCompactSupport (compactTrial n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (compactTrial_support_subset n)

theorem compactTrial_support_inside (n : ℕ) :
    Function.support (compactTrial n) ⊆ Ioo (-3 * scale n) (3 * scale n) := by
  intro t ht
  have hh := compactTrial_support_subset n ht
  have hp := scale_pos n
  constructor <;> linarith [hh.1, hh.2]

theorem compactTrial_memLp_two (n : ℕ) : MemLp (compactTrial n) 2 volume :=
  (compactTrial_contDiff n).continuous.memLp_of_hasCompactSupport
    (compactTrial_hasCompactSupport n)

theorem deriv_compactTrial_memLp_two (n : ℕ) : MemLp (deriv (compactTrial n)) 2 volume :=
  (compactTrial_contDiff n).continuous_deriv_one.memLp_of_hasCompactSupport
    (compactTrial_hasCompactSupport n).deriv

/-- A finite global bound for the actual derivative of the fixed smooth bump. -/
theorem exists_bump_derivative_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M := by
  have hb : ContDiff ℝ 1 (bump : ℝ → ℝ) := bump.contDiff
  obtain ⟨C, hC⟩ := hb.continuous_deriv_one.bounded_above_of_compact_support
    bump.hasCompactSupport.deriv
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro t
  have h := hC t
  rw [Real.norm_eq_abs] at h
  linarith [le_abs_self C]

theorem cutoff_derivative_bound (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M) (n : ℕ) (t : ℝ) :
    |deriv (bump : ℝ → ℝ) (t / scale n) / scale n| ≤ M := by
  rw [abs_div, abs_of_pos (scale_pos n)]
  apply (div_le_iff₀ (scale_pos n)).2
  have hb := hbound (t / scale n)
  have ha := one_le_scale n
  nlinarith

theorem compactTrial_abs_le (n : ℕ) (t : ℝ) : |compactTrial n t| ≤ |logTrial t| := by
  unfold compactTrial
  rw [abs_mul, abs_of_nonneg (cutoff_bounds n t).1]
  exact mul_le_of_le_one_left (abs_nonneg _) (cutoff_bounds n t).2

theorem deriv_compactTrial_abs_le (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M) (n : ℕ) (t : ℝ) :
    |deriv (compactTrial n) t| ≤ M * |logTrial t| + |deriv logTrial t| := by
  rw [deriv_compactTrial]
  calc
    |deriv (bump : ℝ → ℝ) (t / scale n) / scale n * logTrial t +
        cutoff n t * deriv logTrial t| ≤
        |deriv (bump : ℝ → ℝ) (t / scale n) / scale n * logTrial t| +
          |cutoff n t * deriv logTrial t| := abs_add_le _ _
    _ = |deriv (bump : ℝ → ℝ) (t / scale n) / scale n| * |logTrial t| +
          cutoff n t * |deriv logTrial t| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_bounds n t).1]
    _ ≤ M * |logTrial t| + |deriv logTrial t| :=
      add_le_add (mul_le_mul_of_nonneg_right (cutoff_derivative_bound M hM hbound n t)
        (abs_nonneg _))
        (mul_le_of_le_one_left (abs_nonneg _) (cutoff_bounds n t).2)

theorem compactTrial_square_le (n : ℕ) (t : ℝ) :
    compactTrial n t ^ 2 ≤ logTrial t ^ 2 := by
  have h := (sq_le_sq₀ (abs_nonneg (compactTrial n t)) (abs_nonneg (logTrial t))).2
    (compactTrial_abs_le n t)
  simpa only [sq_abs] using h

theorem deriv_compactTrial_square_le (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M) (n : ℕ) (t : ℝ) :
    deriv (compactTrial n) t ^ 2 ≤ 2 * M ^ 2 * logTrial t ^ 2 + 2 * deriv logTrial t ^ 2 := by
  have hpos : 0 ≤ M * |logTrial t| + |deriv logTrial t| := by positivity
  have h := (sq_le_sq₀ (abs_nonneg (deriv (compactTrial n) t)) hpos).2
    (deriv_compactTrial_abs_le M hM hbound n t)
  have hs := sq_nonneg (M * |logTrial t| - |deriv logTrial t|)
  simp only [sq_abs] at h
  nlinarith [sq_abs (logTrial t), sq_abs (deriv logTrial t)]

theorem tendsto_inv_scale : Tendsto (fun n : ℕ => 1 / scale n) atTop (𝓝 (0 : ℝ)) := by
  simpa only [scale] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem tendsto_div_scale (t : ℝ) : Tendsto (fun n => t / scale n) atTop (𝓝 (0 : ℝ)) := by
  simpa only [mul_one_div, mul_zero] using tendsto_inv_scale.const_mul t

theorem cutoff_tendsto_one (t : ℝ) : Tendsto (fun n => cutoff n t) atTop (𝓝 (1 : ℝ)) := by
  have h := bump.continuous.continuousAt.tendsto.comp (tendsto_div_scale t)
  simpa only [bump_at_zero, cutoff, Function.comp_def] using h

theorem cutoff_derivative_tendsto_zero (t : ℝ) :
    Tendsto (fun n => deriv (bump : ℝ → ℝ) (t / scale n) / scale n) atTop (𝓝 (0 : ℝ)) := by
  have hb : ContDiff ℝ 1 (bump : ℝ → ℝ) := bump.contDiff
  have h := hb.continuous_deriv_one.continuousAt.tendsto.comp (tendsto_div_scale t)
  simpa only [div_eq_mul_inv, one_div, mul_zero, Function.comp_def, one_mul] using h.mul tendsto_inv_scale

theorem compactTrial_tendsto (t : ℝ) :
    Tendsto (fun n => compactTrial n t) atTop (𝓝 (logTrial t)) := by
  simpa only [compactTrial, one_mul] using (cutoff_tendsto_one t).mul_const (logTrial t)

theorem deriv_compactTrial_tendsto (t : ℝ) :
    Tendsto (fun n => deriv (compactTrial n) t) atTop (𝓝 (deriv logTrial t)) := by
  simp_rw [deriv_compactTrial]
  simpa only [zero_mul, one_mul, zero_add] using
    ((cutoff_derivative_tendsto_zero t).mul_const (logTrial t)).add
      ((cutoff_tendsto_one t).mul_const (deriv logTrial t))

theorem Wlog_nonneg (t : ℝ) : 0 ≤ GaussianPotential.Wlog t := by
  rw [Wlog_eq_radial]
  unfold radialPotential
  exact mul_nonneg (sq_nonneg _) (bernoulli_bounds _).1

theorem abs_four_sub_Wlog_le (t : ℝ) : |4 - GaussianPotential.Wlog t| ≤ 4 := by
  apply abs_le.mpr
  constructor <;> linarith [Wlog_nonneg t, GaussianPotential.Wlog_le_eight t]

theorem measurable_Wlog : Measurable GaussianPotential.Wlog := by
  have he : GaussianPotential.Wlog = fun t =>
      (Real.exp t) ^ 2 * bernoulliRatio (squareRadius (Real.exp t) - 2) := by
    funext t
    exact Wlog_eq_radial t
  rw [he]
  exact (Real.continuous_exp.measurable.pow_const 2).mul
    (measurable_bernoulliRatio.comp (by unfold squareRadius; fun_prop))

/-- The literal quadratic integrand for a real trial. -/
def quadraticIntegrand (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t ^ 2 + (4 - GaussianPotential.Wlog t) * f t ^ 2

def formBound (M t : ℝ) : ℝ :=
  2 * deriv logTrial t ^ 2 + (2 * M ^ 2 + 4) * logTrial t ^ 2

theorem integrable_formBound (M : ℝ) : Integrable (formBound M) :=
  (integrable_deriv_logTrial_square.const_mul 2).add
    (integrable_logTrial_square.const_mul (2 * M ^ 2 + 4))

theorem quadraticIntegrand_bound (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |deriv (bump : ℝ → ℝ) t| ≤ M) (n : ℕ) (t : ℝ) :
    ‖quadraticIntegrand (compactTrial n) t‖ ≤ formBound M t := by
  unfold quadraticIntegrand formBound
  rw [Real.norm_eq_abs]
  calc
    |deriv (compactTrial n) t ^ 2 + (4 - GaussianPotential.Wlog t) * compactTrial n t ^ 2| ≤
        |deriv (compactTrial n) t ^ 2| +
          |(4 - GaussianPotential.Wlog t) * compactTrial n t ^ 2| := abs_add_le _ _
    _ = deriv (compactTrial n) t ^ 2 +
        |4 - GaussianPotential.Wlog t| * compactTrial n t ^ 2 := by
          simp only [abs_mul, abs_sq]
    _ ≤ deriv (compactTrial n) t ^ 2 + 4 * compactTrial n t ^ 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (abs_four_sub_Wlog_le t)
        (sq_nonneg (compactTrial n t)))
    _ ≤ 2 * deriv logTrial t ^ 2 + (2 * M ^ 2 + 4) * logTrial t ^ 2 := by
      have hd := deriv_compactTrial_square_le M hM hbound n t
      have hf := compactTrial_square_le n t
      nlinarith

theorem measurable_quadraticIntegrand (n : ℕ) :
    Measurable (quadraticIntegrand (compactTrial n)) := by
  unfold quadraticIntegrand
  exact ((compactTrial_contDiff n).continuous_deriv_one.measurable.pow_const 2).add
    ((measurable_const.sub measurable_Wlog).mul
      ((compactTrial_contDiff n).continuous.measurable.pow_const 2))

/-- Actual integrability of every cutoff quadratic form. -/
theorem integrable_quadraticIntegrand (n : ℕ) :
    Integrable (quadraticIntegrand (compactTrial n)) := by
  obtain ⟨M, hM, hbound⟩ := exists_bump_derivative_bound
  apply (integrable_formBound M).mono'
    (measurable_quadraticIntegrand n).aestronglyMeasurable
  filter_upwards [] with t
  exact quadraticIntegrand_bound M hM hbound n t

theorem quadraticIntegrand_tendsto (t : ℝ) :
    Tendsto (fun n => quadraticIntegrand (compactTrial n) t) atTop
      (𝓝 (logEnergyIntegrand t)) := by
  exact ((deriv_compactTrial_tendsto t).pow 2).add
    (((compactTrial_tendsto t).pow 2).const_mul (4 - GaussianPotential.Wlog t))

/-- Actual dominated convergence of the compact-trial quadratic forms. -/
theorem quadratic_integrals_tendsto :
    Tendsto (fun n => ∫ t : ℝ, quadraticIntegrand (compactTrial n) t) atTop
      (𝓝 (∫ t : ℝ, logEnergyIntegrand t)) := by
  obtain ⟨M, hM, hbound⟩ := exists_bump_derivative_bound
  apply tendsto_integral_of_dominated_convergence (formBound M)
    (fun n => (measurable_quadraticIntegrand n).aestronglyMeasurable)
    (integrable_formBound M)
  · intro n
    filter_upwards [] with t
    exact quadraticIntegrand_bound M hM hbound n t
  · filter_upwards [] with t
    exact quadraticIntegrand_tendsto t

theorem compactTrial_tsupport_inside (n : ℕ) :
    tsupport (compactTrial n) ⊆ Ioo (-3 * scale n) (3 * scale n) := by
  have hh : tsupport (compactTrial n) ⊆ Icc (-2 * scale n) (2 * scale n) := by
    change closure (Function.support (compactTrial n)) ⊆ _
    simpa only [isClosed_Icc.closure_eq] using closure_mono (compactTrial_support_subset n)
  intro t ht
  have hb := hh ht
  have hp := scale_pos n
  constructor <;> linarith [hb.1, hb.2]

/-- A compactly supported C¹ real trial of strictly negative Gaussian Sturm form. -/
theorem exists_compact_negative_trial :
    ∃ R : ℝ, 0 < R ∧ ∃ f : ℝ → ℝ,
      ContDiff ℝ 1 f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo (-R) R ∧
      MemLp f 2 volume ∧ MemLp (deriv f) 2 volume ∧
      (∫ t : ℝ, quadraticIntegrand f t) < 0 := by
  have he : ∀ᶠ n in atTop, (∫ t : ℝ, quadraticIntegrand (compactTrial n) t) < 0 :=
    quadratic_integrals_tendsto.eventually (Iio_mem_nhds log_trial_strictly_negative)
  obtain ⟨n, hn⟩ := he.exists
  refine ⟨3 * scale n, mul_pos (by norm_num) (scale_pos n), compactTrial n,
    compactTrial_contDiff n, compactTrial_hasCompactSupport n, ?_,
    compactTrial_memLp_two n, deriv_compactTrial_memLp_two n, hn⟩
  simpa only [neg_mul] using compactTrial_tsupport_inside n

end UnforcedLeray.GaussianCompactTrial
