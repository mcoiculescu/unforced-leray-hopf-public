import UnforcedLeray.Units.B0284.Contraction
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Two-dimensional Gaussian rescaling

The normalized-cell vector heat approximate identity uses the literal planar kernel from B0284.
This is its exact parabolic rescaling formula on `Plane`, proved from the Haar measure scaling law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

/-- Rescaling the actual B0284 planar Gaussian to unit age preserves its probability mass. -/
theorem lintegral_heatKernel2_mul_eq_unit {θ : ℝ} (hθ : 0 < θ)
    (ω : Plane → ℝ≥0∞) :
    ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 θ w) * ω w =
      ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
        ω (Real.sqrt θ • w) := by
  let b := Real.sqrt θ
  have hb : 0 < b := Real.sqrt_pos.mpr hθ
  have hbne : b ≠ 0 := hb.ne'
  have hb2 : b ^ 2 = θ := Real.sq_sqrt hθ.le
  have hkernel : ∀ w : Plane,
      UnforcedLeray.B0284.heatKernel2 θ (b • w) = b⁻¹ ^ 2 *
        UnforcedLeray.B0284.heatKernel2 1 w := by
    intro w
    have hq : B0191.heatKernel 1 θ (b * w.1) =
        b⁻¹ * B0191.heatKernel 1 1 w.1 := by
      rw [B0191.heatKernel_selfSimilar 1 hθ]
      simp only [B0191.profile]
      congr 1
      simp [b, hbne]
    have hη : B0191.heatKernel 1 θ (b * w.2) =
        b⁻¹ * B0191.heatKernel 1 1 w.2 := by
      rw [B0191.heatKernel_selfSimilar 1 hθ]
      simp only [B0191.profile]
      congr 1
      simp [b, hbne]
    change B0191.heatKernel 1 θ (b * w.1) * B0191.heatKernel 1 θ (b * w.2) = _
    rw [hq, hη]
    dsimp [UnforcedLeray.B0284.heatKernel2]
    ring
  let G : Plane → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 θ w) * ω w
  have hmap := MeasureTheory.lintegral_map_equiv G
    (Homeomorph.smul (Units.mk0 b hbne)).toMeasurableEquiv
    (μ := (volume : Measure Plane))
  change ∫⁻ y : Plane, G y ∂Measure.map (fun x : Plane => b • x) volume =
    ∫⁻ x : Plane, G (b • x) at hmap
  rw [Measure.map_addHaar_smul (volume : Measure Plane) hbne,
    lintegral_smul_measure] at hmap
  have hG : (fun w : Plane => G (b • w)) = fun w =>
      ENNReal.ofReal (b⁻¹ ^ 2) *
        (ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) * ω (b • w)) := by
    funext w
    simp only [G, hkernel]
    rw [ENNReal.ofReal_mul (by positivity)]
    ring
  rw [hG, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hmap
  have hfactor : ENNReal.ofReal (b⁻¹ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane]
  have hfactorEq : ENNReal.ofReal |(b ^ Module.finrank ℝ Plane)⁻¹| =
      ENNReal.ofReal (b⁻¹ ^ 2) := by
    rw [hdim, abs_of_pos (inv_pos.mpr (pow_pos hb 2)), inv_pow]
  rw [hfactorEq] at hmap
  have hmap' : ENNReal.ofReal (b⁻¹ ^ 2) * (∫⁻ w : Plane, G w) =
      ENNReal.ofReal (b⁻¹ ^ 2) *
        (∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
          ω (b • w)) := by
    simpa only [smul_eq_mul] using hmap
  exact (ENNReal.mul_right_inj hfactor ENNReal.ofReal_ne_top).mp hmap' 

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.lintegral_heatKernel2_mul_eq_unit
