import UnforcedLeray.Analysis.Sturm.NeutralFactorization
import UnforcedLeray.Analysis.Sturm.TraceZeroApproximation
import UnforcedLeray.Analysis.Sturm.GlobalH1Cutoff

/-!
# The Gaussian form on the zero-trace subspace

Two explicit cutoff constructions extend the ground-state identity first across
the critical point and then to the whole line. The result applies to actual
classical C¹ representatives with value and derivative in L². No trace or
smooth-density theorem is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
namespace UnforcedLeray.Sturm
open GaussianPotential

/-- Removing a shrinking neighborhood of the zero proves positivity for every
compact C¹ trial with exactly zero trace at the critical point. -/
theorem neutral_form_nonneg_compact_trace_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (ha : f neutralCriticalTime = 0) : 0 ≤ quadraticForm 1 f (deriv f) := by
  have hV : Measurable (fun t => 1 - Wlog t) := measurable_const.sub measurable_Wlog
  have hlim := TraceZeroApproximation.integral_form_tendsto hf hfc ha
    (fun t => 1 - Wlog t) hV 9 neutral_form_potential_bound
  change 0 ≤ ∫ t, deriv f t ^ 2 + (1 ^ 2 - Wlog t) * f t ^ 2
  simp only [one_pow]
  apply ge_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  simpa only [quadraticForm, one_pow] using neutral_form_nonneg_away
    (TraceZeroApproximation.removePoint_contDiff hf neutralCriticalTime n)
    (TraceZeroApproximation.removePoint_hasCompactSupport hfc neutralCriticalTime n)
    (TraceZeroApproximation.removePoint_notMem_tsupport neutralCriticalTime f n)

/-- The actual H¹ energy is nonnegative on the critical zero-trace subspace,
for every C¹ representative. Both L² memberships are explicit and standard. -/
theorem neutral_form_nonneg_trace_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 volume)
    (hdf2 : MemLp (deriv f) 2 volume) (ha : f neutralCriticalTime = 0) :
    0 ≤ quadraticForm 1 f (deriv f) := by
  have hV : Measurable (fun t => 1 - Wlog t) := measurable_const.sub measurable_Wlog
  have hlim := GlobalH1Cutoff.integral_form_tendsto hf hf2 hdf2 hV
    (by norm_num : (0 : ℝ) ≤ 9) neutral_form_potential_bound
  simp only [GlobalH1Cutoff.formIntegrand] at hlim
  change 0 ≤ ∫ t, deriv f t ^ 2 + (1 ^ 2 - Wlog t) * f t ^ 2
  simp only [one_pow]
  apply ge_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  simpa only [quadraticForm, one_pow] using neutral_form_nonneg_compact_trace_zero
    (GlobalH1Cutoff.approximation_contDiff hf n)
    (GlobalH1Cutoff.approximation_hasCompactSupport f n)
    (GlobalH1Cutoff.approximation_zero_at ha n)

/-- The manuscript's actual codimension-one coercivity bound, obtained from
its explicit neutral Gaussian profile and genuine cutoff convergence. -/
theorem quadraticForm_trace_zero_coercive {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 volume)
    (hdf2 : MemLp (deriv f) 2 volume) (ha : f neutralCriticalTime = 0) (n : ℝ) :
    (n ^ 2 - 1) * (∫ t, f t ^ 2) ≤ quadraticForm n f (deriv f) := by
  have hnonneg := neutral_form_nonneg_trace_zero hf hf2 hdf2 ha
  rw [quadraticForm_expansion hf2 hdf2] at hnonneg ⊢
  norm_num at hnonneg
  nlinarith

/-- Strict positivity for a nonzero critical-zero-trace function at n²>1. -/
theorem quadraticForm_trace_zero_pos {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 volume)
    (hdf2 : MemLp (deriv f) 2 volume) (ha : f neutralCriticalTime = 0)
    (hz : ¬ f =ᵐ[volume] 0) {n : ℝ} (hn : 1 < n ^ 2) :
    0 < quadraticForm n f (deriv f) := by
  exact lt_of_lt_of_le (mul_pos (sub_pos.mpr hn) (integral_sq_pos hf2 hz))
    (quadraticForm_trace_zero_coercive hf hf2 hdf2 ha n)

end UnforcedLeray.Sturm
