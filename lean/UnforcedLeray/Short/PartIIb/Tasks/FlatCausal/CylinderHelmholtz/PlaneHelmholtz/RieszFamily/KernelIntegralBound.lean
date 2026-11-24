import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneRieszKernelBound

/-!
# Leaf `PartII-b:T12/1/1/2/25`: the off-support bound for the planar Riesz kernel integral

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

If `φ` is integrable and supported at distance at least `δ` from `x`, then the kernel integral
`∫ K_{ik}(x - y) φ(y) dy` is bounded by `(δ²)⁻¹ ∫ |φ|`, using the pointwise bound
`|K_{ik}(z)| ≤ (δ²)⁻¹` for `δ ≤ ‖z‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/25`.**  Off-support bound for `∫ K_{ik}(x - y) φ(y) dy`. -/
theorem kernelIntegralBound : KernelIntegralBound := by
  intro i k φ δ x hφ hδ hsupp
  have hpt : ∀ y, ‖planeRieszKernel i k (x - y) * φ y‖ ≤ (δ ^ 2)⁻¹ * |φ y| := by
    intro y
    by_cases h : φ y = 0
    · simp [h]
    · have hb : |planeRieszKernel i k (x - y)| ≤ (δ ^ 2)⁻¹ :=
        planeRieszKernelBound i k δ (x - y) hδ (hsupp y h)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  calc ‖∫ y, planeRieszKernel i k (x - y) * φ y‖
      ≤ ∫ y, ‖planeRieszKernel i k (x - y) * φ y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (δ ^ 2)⁻¹ * |φ y| :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          (hφ.abs.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = (δ ^ 2)⁻¹ * ∫ y, |φ y| := integral_const_mul _ _

end UnforcedLeray.Short.IIb.PlaneRiesz
