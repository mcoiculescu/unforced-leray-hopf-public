import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneRieszKernelBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszTestOffSupport

/-!
# Leaf `PartII-b:T12/1/1/2/22`: decay of the planar Riesz pair on tests

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula);
classical Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `f` supported in `‖y‖ ≤ ρ` and `‖x‖ ≥ 2|ρ| + 1`, the point `x` lies off the
support, so `S_{ik} f(x) = ∫ K_{ik}(x - y) f(y) dy` (`RieszTestOffSupport`).  On the support
`‖x - y‖ ≥ ‖x‖ / 2`, so the kernel bound `|K_{ik}(z)| ≤ (δ²)⁻¹` for `δ ≤ ‖z‖`
(`PlaneRieszKernelBound`) with `δ = ‖x‖ / 2` gives `|S_{ik} f(x)| ≤ 4 ‖x‖⁻² ∫ |f|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/22`.**  `S_{ik} f = O(‖x‖⁻²)` at infinity for a planar test `f`. -/
theorem rieszTestDecay : RieszTestDecay := by
  intro i k f hf
  obtain ⟨ρ, hρ⟩ := hf.2.isCompact.isBounded.subset_closedBall 0
  have hfi : Integrable f volume := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hsupp : ∀ y, y ∈ tsupport f → ‖y‖ ≤ |ρ| := fun y hy => by
    have := hρ hy
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_abs_self ρ]
  refine ⟨4 * ∫ y, |f y|, 2 * |ρ| + 1, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := by linarith [abs_nonneg ρ]
  have hxt : x ∉ tsupport f := fun h => by
    have := hsupp x h
    linarith [abs_nonneg ρ]
  have h2 : ((‖x‖ / 2) ^ 2)⁻¹ = 4 * (‖x‖ ^ 2)⁻¹ := by
    rw [div_pow, inv_div]
    ring
  have hpt : ∀ y, ‖planeRieszKernel i k (x - y) * f y‖ ≤ 4 * (‖x‖ ^ 2)⁻¹ * |f y| := by
    intro y
    by_cases hy : f y = 0
    · simp [hy]
    · have hy' := hsupp y (subset_tsupport f hy)
      have hd : ‖x‖ / 2 ≤ ‖x - y‖ := by
        have := norm_sub_norm_le x y
        linarith [abs_nonneg ρ]
      have hk : |planeRieszKernel i k (x - y)| ≤ 4 * (‖x‖ ^ 2)⁻¹ :=
        (planeRieszKernelBound i k (‖x‖ / 2) (x - y) (by positivity) hd).trans h2.le
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  have h := norm_integral_le_of_norm_le (hfi.abs.const_mul (4 * (‖x‖ ^ 2)⁻¹))
    (Eventually.of_forall hpt)
  rw [integral_const_mul, Real.norm_eq_abs] at h
  rw [rieszTestOffSupport i k f hf x hxt, Real.rpow_neg (norm_nonneg x), Real.rpow_two]
  exact h.trans (le_of_eq (by ring))

end UnforcedLeray.Short.IIb.PlaneRiesz
