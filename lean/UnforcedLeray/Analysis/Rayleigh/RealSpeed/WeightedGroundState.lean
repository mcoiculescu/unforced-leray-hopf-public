import UnforcedLeray.Analysis.Sturm.NeutralFactorizationBasic
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.WeightedCutoff

/-!
# Whole-line ground-state positivity with an integrable potential product

The compact ground-state identity is passed through the actual local and global
cutoff sequences. The potential need not be bounded; its product with the squared
trial function must be integrable. If the reference profile can vanish at one
point, the trial function has zero trace there. The differential identity is
required only where the reference profile is nonzero.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace UnforcedLeray.Rayleigh.RealSpeed
open UnforcedLeray.Sturm

/-- A compact trial with zero trace at the sole possible zero of the reference
profile has nonnegative actual weighted form. -/
theorem weighted_groundState_nonneg_compact_trace_zero {h f V : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a : ℝ} (ha : f a = 0)
    (hnonzero : ∀ t, t ≠ a → h t ≠ 0)
    (hode : ∀ t, h t ≠ 0 → deriv (deriv h) t = V t * h t)
    (hV : Measurable V) (hpot : Integrable (fun t => V t * f t ^ 2)) :
    0 ≤ ∫ t, deriv f t ^ 2 + V t * f t ^ 2 := by
  apply ge_of_tendsto (local_weighted_form_tendsto hf hc ha hV hpot)
  apply Eventually.of_forall
  intro n
  have hz : ∀ t ∈ tsupport (TraceZeroApproximation.removePoint a f n), h t ≠ 0 := by
    intro t ht
    apply hnonzero t
    intro he
    subst t
    exact TraceZeroApproximation.removePoint_notMem_tsupport a f n ht
  apply groundState_form_nonneg hh
    (TraceZeroApproximation.removePoint_contDiff hf a n)
    (TraceZeroApproximation.removePoint_hasCompactSupport hc a n) hz
    (fun t ht => hode t (hz t ht))
  exact (TraceZeroApproximation.deriv_removePoint_memLp_two hf hc a n).integrable_sq.add
    (local_weighted_integrable hf hV hpot a n)

/-- Whole-line weighted ground-state positivity when the reference profile is
nowhere zero. The actual H¹ hypotheses and potential-product integrability
justify every integral and the cutoff limit. -/
theorem weighted_groundState_nonneg {h f V : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 volume) (hdf2 : MemLp (deriv f) 2 volume)
    (hnonzero : ∀ t, h t ≠ 0)
    (hode : ∀ t, h t ≠ 0 → deriv (deriv h) t = V t * h t)
    (hV : Measurable V) (hpot : Integrable (fun t => V t * f t ^ 2)) :
    0 ≤ ∫ t, deriv f t ^ 2 + V t * f t ^ 2 := by
  apply ge_of_tendsto (global_weighted_form_tendsto hf hf2 hdf2 hV hpot)
  apply Eventually.of_forall
  intro n
  apply groundState_form_nonneg hh
    (GlobalH1Cutoff.approximation_contDiff hf n)
    (GlobalH1Cutoff.approximation_hasCompactSupport f n)
    (fun t _ => hnonzero t) (fun t _ => hode t (hnonzero t))
  exact (GlobalH1Cutoff.deriv_approximation_memLp_two hf n).integrable_sq.add
    (global_weighted_integrable hf hV hpot n)

/-- Whole-line positivity on the actual zero-trace subspace when the reference
profile has at most one zero. No bounded-potential or density premise is used. -/
theorem weighted_groundState_nonneg_trace_zero {h f V : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 volume) (hdf2 : MemLp (deriv f) 2 volume)
    {a : ℝ} (ha : f a = 0)
    (hnonzero : ∀ t, t ≠ a → h t ≠ 0)
    (hode : ∀ t, h t ≠ 0 → deriv (deriv h) t = V t * h t)
    (hV : Measurable V) (hpot : Integrable (fun t => V t * f t ^ 2)) :
    0 ≤ ∫ t, deriv f t ^ 2 + V t * f t ^ 2 := by
  apply ge_of_tendsto (global_weighted_form_tendsto hf hf2 hdf2 hV hpot)
  apply Eventually.of_forall
  intro n
  exact weighted_groundState_nonneg_compact_trace_zero hh
    (GlobalH1Cutoff.approximation_contDiff hf n)
    (GlobalH1Cutoff.approximation_hasCompactSupport f n)
    (GlobalH1Cutoff.approximation_zero_at ha n)
    hnonzero hode hV (global_weighted_integrable hf hV hpot n)

end UnforcedLeray.Rayleigh.RealSpeed
