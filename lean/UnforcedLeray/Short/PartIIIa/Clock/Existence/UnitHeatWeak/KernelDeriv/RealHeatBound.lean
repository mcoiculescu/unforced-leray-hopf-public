import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1_2
import UnforcedLeray.Units.B0284.Contraction

/-!
# Part III-a, `PartIII-a:T21/3/2/1/2/4`: `RealHeatBound` (lemma B')

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
The real heat flow `realHeat τ g y = ∫ G_τ(w) g(y - w)` of a bounded continuous `g` is bounded by
the sup of `|g|` (`∫ G_τ = 1`, `G_τ ≥ 0`) and continuous (dominated convergence with dominant
`K G_τ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

theorem realHeatBound : UnforcedLeray.Short.IIIa.Exist.RealHeatBound := by
  intro g hg K hK τ hτ
  have hGi : Integrable (UnforcedLeray.B0284.heatKernel2 τ) :=
    UnforcedLeray.B0284.integrable_heatKernel2 hτ
  have hG0 : ∀ w, 0 ≤ UnforcedLeray.B0284.heatKernel2 τ w :=
    fun w => UnforcedLeray.B0284.heatKernel2_nonneg hτ w
  have hGc : Continuous (UnforcedLeray.B0284.heatKernel2 τ) := by
    unfold UnforcedLeray.B0284.heatKernel2
    exact (((UnforcedLeray.B0191.contDiff_heatKernel 1 τ).continuous).comp continuous_fst).mul
      (((UnforcedLeray.B0191.contDiff_heatKernel 1 τ).continuous).comp continuous_snd)
  have hmass : ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 τ w * K = K := by
    rw [integral_mul_const, UnforcedLeray.B0284.integral_heatKernel2 hτ, one_mul]
  have hbd : ∀ y, |realHeat τ g y| ≤ K := by
    intro y
    have hmain : ‖∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 τ w * g (y - w)‖ ≤
        ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 τ w * K := by
      apply norm_integral_le_of_norm_le (hGi.mul_const K)
      refine Filter.Eventually.of_forall fun w => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hG0 w)]
      exact mul_le_mul_of_nonneg_left (hK _) (hG0 w)
    have h1 : |realHeat τ g y| =
        ‖∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 τ w * g (y - w)‖ := by
      rw [Real.norm_eq_abs]
      rfl
    rw [h1]
    exact hmain.trans (le_of_eq hmass)
  refine ⟨?_, hbd⟩
  show Continuous fun y : ℝ × ℝ =>
    ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 τ w * g (y - w)
  apply continuous_of_dominated (bound := fun w => UnforcedLeray.B0284.heatKernel2 τ w * K)
  · intro y
    exact (hGc.mul (hg.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · intro y
    refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hG0 w)]
    exact mul_le_mul_of_nonneg_left (hK _) (hG0 w)
  · exact hGi.mul_const K
  · refine Filter.Eventually.of_forall fun w => ?_
    exact (hg.comp (continuous_id.sub continuous_const)).const_mul _

end UnforcedLeray.Short.IIIa.Exist
