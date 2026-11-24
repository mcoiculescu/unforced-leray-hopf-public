import UnforcedLeray.GaussianCompactTrial
import UnforcedLeray.Analysis.Sturm.QuadraticForm
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Removing a trace-zero point by explicit smooth cutoffs

For a compact C¹ real function vanishing at a point, the actual cutoffs
`(1 - bump ((n+1)*(t-a))) * f t` vanish in a neighborhood of that point and
converge in the first-order energy norm. The bound on the shrinking-cutoff
term follows from the mean value theorem and the zero trace. No endpoint
density theorem is assumed.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace UnforcedLeray.Sturm.TraceZeroApproximation
open GaussianCompactTrial

/-- Remove an actual neighborhood of the specified point. -/
def removePoint (a : ℝ) (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (1 - bump (scale n * (t - a))) * f t

theorem removePoint_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a : ℝ) (n : ℕ) :
    ContDiff ℝ 1 (removePoint a f n) := by
  exact (contDiff_const.sub (bump.contDiff.comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const)))).mul hf

theorem removePoint_contDiff_infty {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (a : ℝ) (n : ℕ) : ContDiff ℝ ∞ (removePoint a f n) := by
  exact (contDiff_const.sub (bump.contDiff.comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const)))).mul hf

theorem removePoint_tsupport_subset (a : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    tsupport (removePoint a f n) ⊆ tsupport f := tsupport_mul_subset_right

theorem removePoint_hasCompactSupport {f : ℝ → ℝ} (hf : HasCompactSupport f)
    (a : ℝ) (n : ℕ) : HasCompactSupport (removePoint a f n) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (removePoint_tsupport_subset a f n)

theorem removePoint_notMem_tsupport (a : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    a ∉ tsupport (removePoint a f n) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  have hc : Continuous (fun t : ℝ => scale n * (t - a)) := by fun_prop
  have hh : ∀ᶠ t in 𝓝 a, scale n * (t - a) ∈ Metric.ball 0 1 := by
    exact hc.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hh] with t ht
  have hb : bump (scale n * (t - a)) = 1 :=
    bump.one_of_mem_closedBall (Metric.ball_subset_closedBall ht)
  simp [removePoint, hb]

theorem hasDerivAt_removePoint {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (a : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (removePoint a f n)
      (-(deriv (bump : ℝ → ℝ) (scale n * (t - a)) * scale n) * f t +
        (1 - bump (scale n * (t - a))) * deriv f t) t := by
  have hb : ContDiff ℝ 1 (bump : ℝ → ℝ) := bump.contDiff
  convert ((hasDerivAt_const t 1).sub
    (((hb.differentiable (by norm_num) _).hasDerivAt).comp t
      (((hasDerivAt_id t).sub_const a).const_mul (scale n)))).mul
        (hf.differentiable (by norm_num) t).hasDerivAt using 1 <;>
    first | rfl | simp [Pi.sub_apply, Function.comp_def]

theorem deriv_removePoint {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (a : ℝ) (n : ℕ) (t : ℝ) :
    deriv (removePoint a f n) t =
      -(deriv (bump : ℝ → ℝ) (scale n * (t - a)) * scale n) * f t +
        (1 - bump (scale n * (t - a))) * deriv f t :=
  (hasDerivAt_removePoint hf a n t).deriv

/-- The zero trace gives a linear pointwise bound by a global derivative bound. -/
theorem abs_le_dist_of_trace_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a C : ℝ} (ha : f a = 0) (hC : ∀ t, |deriv f t| ≤ C) (t : ℝ) :
    |f t| ≤ C * |t - a| := by
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (univ : Set ℝ)) (f := f) (C := C)
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => by simpa only [Real.norm_eq_abs] using hC x)
    convex_univ (mem_univ a) (mem_univ t)
  simpa only [ha, sub_zero, Real.norm_eq_abs] using hm

/-- Away from the inner point the cutoff eventually becomes exactly one. -/
theorem eventually_removePoint_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (a t : ℝ) (ht : t ≠ a) :
    ∀ᶠ n : ℕ in atTop,
      removePoint a f n t = f t ∧ deriv (removePoint a f n) t = deriv f t := by
  have hd : 0 < |t - a| := abs_pos.mpr (sub_ne_zero.mpr ht)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / |t - a|)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbig : 2 < |scale n * (t - a)| := by
    rw [abs_mul, abs_of_pos (scale_pos n)]
    have hh : 2 < (N : ℝ) * |t - a| := (div_lt_iff₀ hd).mp hN
    unfold scale
    nlinarith
  have hnot : scale n * (t - a) ∉ tsupport (bump : ℝ → ℝ) := by
    rw [bump.tsupport_eq]
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, bump] using not_le.mpr hbig
  have hb := image_eq_zero_of_notMem_tsupport hnot
  have hdb := deriv_of_notMem_tsupport hnot
  simp [removePoint, deriv_removePoint hf, hb, hdb]

/-- The derivative supported in the shrinking annulus is uniformly controlled
by the zero trace. The factor `scale n` is cancelled by the distance to `a`. -/
theorem cutoff_error_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a C M : ℝ} (ha : f a = 0) (hC0 : 0 ≤ C) (hM0 : 0 ≤ M)
    (hC : ∀ t, |deriv f t| ≤ C)
    (hM : ∀ t, |deriv (bump : ℝ → ℝ) t| ≤ M) (n : ℕ) (t : ℝ) :
    |deriv (bump : ℝ → ℝ) (scale n * (t - a)) * scale n * f t| ≤ 2 * M * C := by
  by_cases hz : deriv (bump : ℝ → ℝ) (scale n * (t - a)) = 0
  · simp only [hz, zero_mul, abs_zero]
    positivity
  · have hm : scale n * (t - a) ∈ tsupport (bump : ℝ → ℝ) :=
      support_deriv_subset hz
    rw [bump.tsupport_eq] at hm
    have hs : scale n * |t - a| ≤ 2 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero,
        abs_mul, abs_of_pos (scale_pos n), bump] using hm
    rw [abs_mul, abs_mul, abs_of_pos (scale_pos n)]
    calc
      |deriv (bump : ℝ → ℝ) (scale n * (t - a))| * scale n * |f t| ≤
          M * scale n * (C * |t - a|) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_right (hM _) (scale_pos n).le)
              (abs_le_dist_of_trace_zero hf ha hC t) (abs_nonneg _)
              (mul_nonneg hM0 (scale_pos n).le)
      _ = M * C * (scale n * |t - a|) := by ring
      _ ≤ M * C * 2 := mul_le_mul_of_nonneg_left hs (mul_nonneg hM0 hC0)
      _ = 2 * M * C := by ring

theorem removePoint_abs_le (a : ℝ) (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    |removePoint a f n t| ≤ |f t| := by
  unfold removePoint
  rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr bump.le_one)]
  exact mul_le_of_le_one_left (abs_nonneg _) (sub_le_self _ bump.nonneg)

theorem deriv_removePoint_abs_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a C M : ℝ} (ha : f a = 0) (hC0 : 0 ≤ C) (hM0 : 0 ≤ M)
    (hC : ∀ t, |deriv f t| ≤ C)
    (hM : ∀ t, |deriv (bump : ℝ → ℝ) t| ≤ M) (n : ℕ) (t : ℝ) :
    |deriv (removePoint a f n) t| ≤ 2 * M * C + C := by
  rw [deriv_removePoint hf]
  calc
    |-(deriv (bump : ℝ → ℝ) (scale n * (t - a)) * scale n) * f t +
        (1 - bump (scale n * (t - a))) * deriv f t| ≤
      |deriv (bump : ℝ → ℝ) (scale n * (t - a)) * scale n * f t| +
        (1 - bump (scale n * (t - a))) * |deriv f t| := by
      simpa only [neg_mul, abs_neg, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr bump.le_one)] using abs_add_le
        (-(deriv (bump : ℝ → ℝ) (scale n * (t - a)) * scale n) * f t)
        ((1 - bump (scale n * (t - a))) * deriv f t)
    _ ≤ 2 * M * C + C := add_le_add (cutoff_error_bound hf ha hC0 hM0 hC hM n t)
      ((mul_le_of_le_one_left (abs_nonneg _) (sub_le_self _ bump.nonneg)).trans (hC t))

theorem exists_function_derivative_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ (∀ t, |f t| ≤ B) ∧ (∀ t, |deriv f t| ≤ C) := by
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨C, hC⟩ := hf.continuous_deriv_one.bounded_above_of_compact_support hc.deriv
  refine ⟨|B|, |C|, abs_nonneg _, abs_nonneg _, ?_, ?_⟩
  · intro t
    have hh : |f t| ≤ B := by simpa only [Real.norm_eq_abs] using hB t
    exact hh.trans (le_abs_self B)
  · intro t
    have hh : |deriv f t| ≤ C := by simpa only [Real.norm_eq_abs] using hC t
    exact hh.trans (le_abs_self C)

/-- A compact support and a uniform bound provide the integrable majorant used below. -/
theorem integral_tendsto_of_compact_uniform_bound {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {K : Set ℝ} (hK : IsCompact K) (C : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n))
    (hsupp : ∀ n t, t ∉ K → F n t = 0)
    (hbound : ∀ n t, ‖F n t‖ ≤ C)
    (hlim : ∀ᵐ t, Tendsto (fun n => F n t) atTop (𝓝 (f t))) :
    Tendsto (fun n => ∫ t, F n t) atTop (𝓝 (∫ t, f t)) := by
  apply tendsto_integral_of_dominated_convergence (K.indicator (fun _ => C)) hF
    ((integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet)
  · intro n
    filter_upwards [] with t
    by_cases ht : t ∈ K
    · simpa only [indicator_of_mem ht] using hbound n t
    · simp only [indicator_of_notMem ht, hsupp n t ht, norm_zero, le_refl]
  · exact hlim

/-- The actual quadratic form integrals converge for every bounded measurable potential. -/
theorem integral_form_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {a : ℝ} (ha : f a = 0)
    (V : ℝ → ℝ) (hV : Measurable V) (L : ℝ) (hL : ∀ t, |V t| ≤ L) :
    Tendsto (fun n => ∫ t, deriv (removePoint a f n) t ^ 2 + V t * removePoint a f n t ^ 2)
      atTop (𝓝 (∫ t, deriv f t ^ 2 + V t * f t ^ 2)) := by
  obtain ⟨B, C, hB0, hC0, hB, hC⟩ := exists_function_derivative_bounds hf hc
  obtain ⟨M, hM0, hM⟩ := exists_bump_derivative_bound
  have hL0 : 0 ≤ L := (abs_nonneg (V 0)).trans (hL 0)
  apply integral_tendsto_of_compact_uniform_bound hc
    ((2 * M * C + C) ^ 2 + L * B ^ 2)
  · intro n
    exact (((removePoint_contDiff hf a n).continuous_deriv_one.measurable.pow_const 2).add
      (hV.mul ((removePoint_contDiff hf a n).continuous.measurable.pow_const 2))).aestronglyMeasurable
  · intro n t ht
    have hfn := image_eq_zero_of_notMem_tsupport
      (fun hmem => ht (removePoint_tsupport_subset a f n hmem))
    have hd := deriv_of_notMem_tsupport
      (fun hmem => ht (removePoint_tsupport_subset a f n hmem))
    simp [hfn, hd]
  · intro n t
    have hfun : |removePoint a f n t| ≤ B := (removePoint_abs_le a f n t).trans (hB t)
    have hder := deriv_removePoint_abs_le hf ha hC0 hM0 hC hM n t
    rw [Real.norm_eq_abs]
    calc
      |deriv (removePoint a f n) t ^ 2 + V t * removePoint a f n t ^ 2| ≤
          deriv (removePoint a f n) t ^ 2 + |V t| * removePoint a f n t ^ 2 := by
            have hh := abs_add_le (deriv (removePoint a f n) t ^ 2)
              (V t * removePoint a f n t ^ 2)
            rw [abs_of_nonneg (sq_nonneg (deriv (removePoint a f n) t)),
              abs_mul, abs_of_nonneg (sq_nonneg (removePoint a f n t))] at hh
            exact hh
      _ ≤ (2 * M * C + C) ^ 2 + L * B ^ 2 := by
        have hsqf : removePoint a f n t ^ 2 ≤ B ^ 2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB0).mpr hfun
        have hsqd : deriv (removePoint a f n) t ^ 2 ≤ (2 * M * C + C) ^ 2 := by
          have hp : 0 ≤ 2 * M * C + C := by positivity
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hp).mpr hder
        exact add_le_add hsqd (mul_le_mul (hL t) hsqf (sq_nonneg _) hL0)
  · filter_upwards [ae_iff.mpr (by simp : volume {t : ℝ | ¬ t ≠ a} = 0)] with t ht
    have he := eventually_removePoint_eq hf a t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    simp only [hn.1, hn.2]

/-- Actual convergence of both the value and derivative errors in squared L² norm. -/
theorem integral_H1_error_tendsto_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {a : ℝ} (ha : f a = 0) :
    Tendsto (fun n => ∫ t, (removePoint a f n t - f t) ^ 2 +
      (deriv (removePoint a f n) t - deriv f t) ^ 2) atTop (𝓝 0) := by
  obtain ⟨B, C, hB0, hC0, hB, hC⟩ := exists_function_derivative_bounds hf hc
  obtain ⟨M, hM0, hM⟩ := exists_bump_derivative_bound
  suffices hh : Tendsto (fun n : ℕ => ∫ t : ℝ, (removePoint a f n t - f t) ^ 2 +
    (deriv (removePoint a f n) t - deriv f t) ^ 2)
    (atTop : Filter ℕ) (𝓝 (∫ _ : ℝ, (0 : ℝ))) by
      simpa only [integral_zero] using hh
  apply integral_tendsto_of_compact_uniform_bound hc
    ((2 * B) ^ 2 + (2 * M * C + 2 * C) ^ 2)
  · intro n
    exact ((((removePoint_contDiff hf a n).continuous.sub hf.continuous).pow 2).add
      (((removePoint_contDiff hf a n).continuous_deriv_one.sub hf.continuous_deriv_one).pow 2)).aestronglyMeasurable
  · intro n t ht
    have hfn := image_eq_zero_of_notMem_tsupport
      (fun hmem => ht (removePoint_tsupport_subset a f n hmem))
    have hdn := deriv_of_notMem_tsupport
      (fun hmem => ht (removePoint_tsupport_subset a f n hmem))
    simp only [hfn, hdn, image_eq_zero_of_notMem_tsupport ht,
      deriv_of_notMem_tsupport ht, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  · intro n t
    have hfun : |removePoint a f n t - f t| ≤ 2 * B := by
      calc
        |removePoint a f n t - f t| ≤ |removePoint a f n t| + |f t| :=
          by simpa only [Real.norm_eq_abs] using norm_sub_le (removePoint a f n t) (f t)
        _ ≤ B + B := add_le_add ((removePoint_abs_le a f n t).trans (hB t)) (hB t)
        _ = 2 * B := by ring
    have hder : |deriv (removePoint a f n) t - deriv f t| ≤ 2 * M * C + 2 * C := by
      calc
        |deriv (removePoint a f n) t - deriv f t| ≤
            |deriv (removePoint a f n) t| + |deriv f t| :=
          by simpa only [Real.norm_eq_abs] using norm_sub_le (deriv (removePoint a f n) t) (deriv f t)
        _ ≤ (2 * M * C + C) + C := add_le_add
          (deriv_removePoint_abs_le hf ha hC0 hM0 hC hM n t) (hC t)
        _ = 2 * M * C + 2 * C := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    apply add_le_add
    · simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * B)).mpr hfun
    · simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * M * C + 2 * C)).mpr hder
  · filter_upwards [ae_iff.mpr (by simp : volume {t : ℝ | ¬ t ≠ a} = 0)] with t ht
    have he := eventually_removePoint_eq hf a t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    simp only [hn.1, hn.2, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]

theorem removePoint_memLp_two {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (a : ℝ) (n : ℕ) :
    MemLp (removePoint a f n) 2 volume :=
  (removePoint_contDiff hf a n).continuous.memLp_of_hasCompactSupport
    (removePoint_hasCompactSupport hc a n)

theorem deriv_removePoint_memLp_two {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (a : ℝ) (n : ℕ) :
    MemLp (deriv (removePoint a f n)) 2 volume :=
  (removePoint_contDiff hf a n).continuous_deriv_one.memLp_of_hasCompactSupport
    (removePoint_hasCompactSupport hc a n).deriv

end UnforcedLeray.Sturm.TraceZeroApproximation
