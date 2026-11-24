import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# From squared complex L² error to strong quotient convergence

The finite integral of the actual pointwise squared error is identified with
the squared norm of the difference of L² classes. Continuity of the real
square root then gives strong L² convergence. All functions carry `MemLp`
hypotheses, so no default quotient or nonintegrable integral is used.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace UnforcedLeray.Sturm.ComplexL2Convergence

/-- The Hilbert norm of the actual complex L² class is its squared integral. -/
theorem norm_sq_eq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Passing to the L² quotient preserves the literal finite squared norm. -/
theorem norm_toLp_sq {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  exact integral_congr_ae (hf.coeFn_toLp.mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx)

/-- The quotient difference norm is the actual squared error integral. -/
theorem norm_toLp_sub_sq {f g : ℝ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x : ℝ, ‖f x - g x‖ ^ 2 := by
  rw [← hf.toLp_sub hg, norm_toLp_sq]
  rfl

/-- Squared integral convergence gives norm convergence of the actual L² classes. -/
theorem norm_toLp_sub_tendsto_zero {f : ℝ → ℂ} {F : ℕ → ℝ → ℂ}
    (hf : MemLp f 2 volume) (hF : ∀ n, MemLp (F n) 2 volume)
    (herr : Tendsto (fun n => ∫ x : ℝ, ‖F n x - f x‖ ^ 2) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ‖(hF n).toLp (F n) - hf.toLp f‖) atTop (𝓝 (0 : ℝ)) := by
  have hs : Tendsto (fun n => ‖(hF n).toLp (F n) - hf.toLp f‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_toLp_sub_sq] using herr
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hroot

/-- Strong L² convergence follows from an actual vanishing squared error integral. -/
theorem toLp_tendsto_of_integral_error {f : ℝ → ℂ} {F : ℕ → ℝ → ℂ}
    (hf : MemLp f 2 volume) (hF : ∀ n, MemLp (F n) 2 volume)
    (herr : Tendsto (fun n => ∫ x : ℝ, ‖F n x - f x‖ ^ 2) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using norm_toLp_sub_tendsto_zero hf hF herr

/-- The usual finite real-valued L² seminorm of the error also tends to zero. -/
theorem eLpNorm_toReal_error_tendsto_zero {f : ℝ → ℂ} {F : ℕ → ℝ → ℂ}
    (hf : MemLp f 2 volume) (hF : ∀ n, MemLp (F n) 2 volume)
    (herr : Tendsto (fun n => ∫ x : ℝ, ‖F n x - f x‖ ^ 2) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => (eLpNorm (fun x => F n x - f x) 2 volume).toReal)
      atTop (𝓝 (0 : ℝ)) := by
  have he : ∀ n, (eLpNorm (fun x => F n x - f x) 2 volume).toReal =
      ‖(hF n).toLp (F n) - hf.toLp f‖ := by
    intro n
    rw [← (hF n).toLp_sub hf, Lp.norm_toLp]
    rfl
  simpa only [he] using norm_toLp_sub_tendsto_zero hf hF herr

end UnforcedLeray.Sturm.ComplexL2Convergence
