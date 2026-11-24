import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs

/-!
# Dominated convergence for the planar cutoffs

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula);
Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

For a cutoff family `χ_R` (`0 ≤ χ_R ≤ 1`, `χ_R = 1` on `‖x‖ ≤ R`), `χ_R g → g` pointwise
and `|χ_R g| ≤ |g|`, so `∫ χ_R g → ∫ g` for integrable `g` (dominated convergence on `atTop`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- Dominated convergence for the cutoffs (`DominatedCutoffLimit`). -/
theorem dominatedCutoffLimit : DominatedCutoffLimit := by
  intro χ hχ g hg
  have hlim : ∀ x : Pl, ∀ᶠ R in atTop, χ R x * g x = g x := by
    intro x
    filter_upwards [eventually_ge_atTop (max 1 ‖x‖)] with R hR
    have h1 : 1 ≤ R := le_trans (le_max_left _ _) hR
    have h2 : ‖x‖ ≤ R := le_trans (le_max_right _ _) hR
    rw [hχ.2.2.1 R x h1 h2, one_mul]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => |g x|) ?_ ?_ hg.abs ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact (((hχ.1 R hR).1.continuous).aestronglyMeasurable.mul hg.aestronglyMeasurable)
  · refine Eventually.of_forall (fun R => ?_)
    refine ae_of_all _ (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ.2.1 R x).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hχ.2.1 R x).2
  · exact ae_of_all _ (fun x => (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (hlim x))))

end UnforcedLeray.Short.IIb.PlaneRiesz
