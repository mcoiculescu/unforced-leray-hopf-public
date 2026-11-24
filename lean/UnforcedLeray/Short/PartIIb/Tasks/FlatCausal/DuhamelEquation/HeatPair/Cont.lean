import UnforcedLeray.Short.PartIIb.Sub.T12_7_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.FlatHeatContraction

/-!
# Part II-b, task `PartII-b:T12/7/4/1` (`deqhpCont`): continuity of the smoothed test

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
For `s > t` the map `z ↦ ∫ K_θ(w) Ψ(s, z - w)_i dw` (`θ = ν(s-t) > 0`) is continuous: the
integrand is continuous in `z`, and dominated by `M K_θ(w)` where `M` bounds the compactly
supported continuous function `Ψ_i`, which is integrable against the heat kernel.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem deqhpCont : DeqhpCont := by
  intro ν t hν Ψ hΨ i s hts
  have hθ : 0 < ν * (s - t) := mul_pos hν (by linarith)
  have hgc : Continuous (fun x : Coord => Ψ x i) := (hΨ.smooth i).smooth.continuous
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support (hΨ.smooth i).compact
  have hgs : Continuous (fun y : ℝ × ℝ => Ψ (s, y) i) := hgc.comp (continuous_const.prodMk continuous_id)
  have hsm : deqSmooth ν Ψ i t s = fun z : ℝ × ℝ =>
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * (s - t)) w * Ψ (s, z - w) i := by
    funext z
    simp only [deqSmooth, flatHeat_kernel_eq hθ]
  rw [hsm]
  refine continuous_of_dominated (bound := fun w => UnforcedLeray.B0284.heatKernel2 (ν * (s - t)) w * M)
    ?_ ?_ ?_ ?_
  · intro z
    exact (UnforcedLeray.B0284.measurable_heatKernel2_right _).aestronglyMeasurable.mul
      (hgs.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · intro z
    refine Eventually.of_forall fun w => ?_
    rw [norm_mul, Real.norm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
    exact mul_le_mul_of_nonneg_left (hM _) (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)
  · exact (UnforcedLeray.B0284.integrable_heatKernel2 hθ).mul_const M
  · exact Eventually.of_forall fun w =>
      continuous_const.mul (hgs.comp (continuous_id.sub continuous_const))

end UnforcedLeray.Short.IIb

end
