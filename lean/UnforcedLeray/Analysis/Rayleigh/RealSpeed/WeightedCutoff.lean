import UnforcedLeray.Analysis.Sturm.TraceZeroApproximation
import UnforcedLeray.Analysis.Sturm.GlobalH1Cutoff

/-!
# Cutoff limits with an integrable, possibly unbounded potential term

An actual integrable product `V*f²` suffices for convergence of the potential
energy under either cutoff. The majorant is its absolute value; no global bound
on `V` is required. The derivative energy limits use the previously proved
explicit cutoff estimates. Applications must supply product integrability,
for example from their actual differential equation.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace UnforcedLeray.Rayleigh.RealSpeed
open UnforcedLeray.Sturm

/-- Decreasing the absolute value of a field decreases its weighted square norm. -/
theorem weighted_square_norm_le {f g V : ℝ → ℝ}
    (habs : ∀ t, |g t| ≤ |f t|) (t : ℝ) :
    ‖V t * g t ^ 2‖ ≤ ‖V t * f t ^ 2‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_sq, abs_sq]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (habs t)

/-- The original weighted product supplies the integrable majorant. -/
theorem integrable_weighted_square_of_abs_le {f g V : ℝ → ℝ}
    (hV : Measurable V) (hg : Measurable g)
    (hpot : Integrable (fun t => V t * f t ^ 2))
    (habs : ∀ t, |g t| ≤ |f t|) :
    Integrable (fun t => V t * g t ^ 2) := by
  apply hpot.norm.mono' (hV.mul (hg.pow_const 2)).aestronglyMeasurable
  exact Eventually.of_forall (weighted_square_norm_le habs)

/-- Dominated convergence using precisely the actual original weighted product. -/
theorem weighted_integral_tendsto_of_abs_le {F : ℕ → ℝ → ℝ} {f V : ℝ → ℝ}
    (hV : Measurable V) (hF : ∀ n, Measurable (F n))
    (hpot : Integrable (fun t => V t * f t ^ 2))
    (habs : ∀ n t, |F n t| ≤ |f t|)
    (hlim : ∀ᵐ t, Tendsto (fun n => F n t) atTop (𝓝 (f t))) :
    Tendsto (fun n => ∫ t, V t * F n t ^ 2) atTop
      (𝓝 (∫ t, V t * f t ^ 2)) := by
  apply tendsto_integral_of_dominated_convergence (fun t => ‖V t * f t ^ 2‖)
    (fun n => (hV.mul ((hF n).pow_const 2)).aestronglyMeasurable) hpot.norm
  · intro n
    exact Eventually.of_forall (weighted_square_norm_le (habs n))
  · filter_upwards [hlim] with t ht
    exact (ht.pow 2).const_mul (V t)

/-- Every local cutoff has a convergent potential integral. -/
theorem local_weighted_integrable {f V : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hV : Measurable V) (hpot : Integrable (fun t => V t * f t ^ 2))
    (a : ℝ) (n : ℕ) :
    Integrable (fun t => V t * TraceZeroApproximation.removePoint a f n t ^ 2) :=
  integrable_weighted_square_of_abs_le hV
    (TraceZeroApproximation.removePoint_contDiff hf a n).continuous.measurable
    hpot (TraceZeroApproximation.removePoint_abs_le a f n)

/-- The local potential limit does not require a bounded potential. -/
theorem local_weighted_potential_tendsto {f V : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hV : Measurable V) (hpot : Integrable (fun t => V t * f t ^ 2)) (a : ℝ) :
    Tendsto (fun n => ∫ t, V t * TraceZeroApproximation.removePoint a f n t ^ 2)
      atTop (𝓝 (∫ t, V t * f t ^ 2)) := by
  apply weighted_integral_tendsto_of_abs_le hV
    (fun n => (TraceZeroApproximation.removePoint_contDiff hf a n).continuous.measurable)
    hpot (TraceZeroApproximation.removePoint_abs_le a f)
  filter_upwards [ae_iff.mpr (by simp : volume {t : ℝ | ¬ t ≠ a} = 0)] with t ht
  apply tendsto_const_nhds.congr'
  filter_upwards [TraceZeroApproximation.eventually_removePoint_eq hf a t ht] with n hn
  exact hn.1.symm

/-- The local cutoffs preserve the squared mass in the limit. -/
theorem local_mass_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 volume) (a : ℝ) :
    Tendsto (fun n => ∫ t, TraceZeroApproximation.removePoint a f n t ^ 2)
      atTop (𝓝 (∫ t, f t ^ 2)) := by
  simpa only [one_mul] using local_weighted_potential_tendsto
    (V := fun _ => 1) hf measurable_const (by simpa only [one_mul] using hf2.integrable_sq) a

/-- Splitting the weighted form is justified by its actual integrability. -/
theorem weighted_form_integral_eq_sum {f V : ℝ → ℝ}
    (hdf2 : MemLp (deriv f) 2 volume)
    (hpot : Integrable (fun t => V t * f t ^ 2)) :
    (∫ t, deriv f t ^ 2 + V t * f t ^ 2) =
      (∫ t, deriv f t ^ 2) + (∫ t, V t * f t ^ 2) :=
  integral_add hdf2.integrable_sq hpot

/-- Full local form convergence for a compact C¹ function with zero trace. -/
theorem local_weighted_form_tendsto {f V : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {a : ℝ} (ha : f a = 0)
    (hV : Measurable V) (hpot : Integrable (fun t => V t * f t ^ 2)) :
    Tendsto (fun n => ∫ t, deriv (TraceZeroApproximation.removePoint a f n) t ^ 2 +
      V t * TraceZeroApproximation.removePoint a f n t ^ 2) atTop
      (𝓝 (∫ t, deriv f t ^ 2 + V t * f t ^ 2)) := by
  have hd : Tendsto (fun n => ∫ t, deriv (TraceZeroApproximation.removePoint a f n) t ^ 2)
      atTop (𝓝 (∫ t, deriv f t ^ 2)) := by
    simpa only [zero_mul, add_zero] using TraceZeroApproximation.integral_form_tendsto
      hf hc ha (fun _ => 0) measurable_const 0 (fun _ => by simp)
  have hp := local_weighted_potential_tendsto hf hV hpot a
  have hfder : MemLp (deriv f) 2 volume :=
    hf.continuous_deriv_one.memLp_of_hasCompactSupport hc.deriv
  have he (n : ℕ) := weighted_form_integral_eq_sum
    (TraceZeroApproximation.deriv_removePoint_memLp_two hf hc a n)
    (local_weighted_integrable hf hV hpot a n)
  simpa only [he, weighted_form_integral_eq_sum hfder hpot] using hd.add hp

/-- Every outer cutoff has a convergent potential integral. -/
theorem global_weighted_integrable {f V : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hV : Measurable V) (hpot : Integrable (fun t => V t * f t ^ 2)) (n : ℕ) :
    Integrable (fun t => V t * GlobalH1Cutoff.approximation f n t ^ 2) :=
  integrable_weighted_square_of_abs_le hV
    (GlobalH1Cutoff.approximation_contDiff hf n).continuous.measurable
    hpot (GlobalH1Cutoff.approximation_abs_le f n)

/-- The outer potential limit uses only product integrability. -/
theorem global_weighted_potential_tendsto {f V : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hV : Measurable V) (hpot : Integrable (fun t => V t * f t ^ 2)) :
    Tendsto (fun n => ∫ t, V t * GlobalH1Cutoff.approximation f n t ^ 2)
      atTop (𝓝 (∫ t, V t * f t ^ 2)) :=
  weighted_integral_tendsto_of_abs_le hV
    (fun n => (GlobalH1Cutoff.approximation_contDiff hf n).continuous.measurable)
    hpot (GlobalH1Cutoff.approximation_abs_le f)
    (Eventually.of_forall (GlobalH1Cutoff.approximation_tendsto f))

/-- The outer cutoffs preserve the squared mass in the limit. -/
theorem global_mass_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 volume) :
    Tendsto (fun n => ∫ t, GlobalH1Cutoff.approximation f n t ^ 2)
      atTop (𝓝 (∫ t, f t ^ 2)) := by
  simpa only [one_mul] using global_weighted_potential_tendsto
    (V := fun _ => 1) hf measurable_const (by simpa only [one_mul] using hf2.integrable_sq)

/-- Full global form convergence with an actually integrable weighted product. -/
theorem global_weighted_form_tendsto {f V : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 volume) (hdf2 : MemLp (deriv f) 2 volume)
    (hV : Measurable V) (hpot : Integrable (fun t => V t * f t ^ 2)) :
    Tendsto (fun n => ∫ t, deriv (GlobalH1Cutoff.approximation f n) t ^ 2 +
      V t * GlobalH1Cutoff.approximation f n t ^ 2) atTop
      (𝓝 (∫ t, deriv f t ^ 2 + V t * f t ^ 2)) := by
  have hd : Tendsto (fun n => ∫ t, deriv (GlobalH1Cutoff.approximation f n) t ^ 2)
      atTop (𝓝 (∫ t, deriv f t ^ 2)) := by
    simpa only [GlobalH1Cutoff.formIntegrand, zero_mul, add_zero] using
      GlobalH1Cutoff.integral_form_tendsto (V := fun _ => 0) hf hf2 hdf2 measurable_const
        (B := 0) le_rfl (fun _ => by simp)
  have hp := global_weighted_potential_tendsto hf hV hpot
  have he (n : ℕ) := weighted_form_integral_eq_sum
    (GlobalH1Cutoff.deriv_approximation_memLp_two hf n)
    (global_weighted_integrable hf hV hpot n)
  simpa only [he, weighted_form_integral_eq_sum hdf2 hpot] using hd.add hp

end UnforcedLeray.Rayleigh.RealSpeed
