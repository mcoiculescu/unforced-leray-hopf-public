import UnforcedLeray.Lib.HeatCylinder.CenteredGaussianShiftAveragePairing
import UnforcedLeray.Lib.HeatCylinder.SmoothBounds
import UnforcedLeray.Lib.CylinderB.Leray

/-!
# Cell Fubini for smooth periodic Gaussian pairings

The scalar joint integrand is integrable because its input factor is globally bounded and its
smooth compact-axial test factor is integrable on the cylinder cell. This is the analytic gate
for identifying the actual Gaussian convolution with the Bochner average of translations.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (cellμ)
open UnforcedLeray.B0284 (heatKernel2)

/-- The actual kernel pairing on `Plane_w × cell_z` is integrable for smooth periodic
compact-axial input and test fields. -/
theorem integrable_heatVecGaussianPairingProduct {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T U : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hU : UnforcedLeray.Sob.IsCylSmooth c U) :
    Integrable (fun p : Plane × Plane =>
      heatKernel2 θ p.1 * ⟪T (p.2 - p.1), U p.2⟫_ℝ)
      ((volume : Measure Plane).prod (cellμ c)) := by
  obtain ⟨M, hM, hTbound⟩ := exists_global_bound_of_cylSmooth hc hT
  have hkernel : Integrable (heatKernel2 θ) :=
    UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hUnorm : Integrable (fun z : Plane => ‖U z‖) (cellμ c) := by
    have hUon : IntegrableOn U (UnforcedLeray.Sob.cylCell c) := hU.integrableOn
    have hUcell : Integrable U (cellμ c) := by
      rw [UnforcedLeray.Cyl.cellμ, UnforcedLeray.Sob.cyl_cell_eq]
      exact hUon
    exact hUcell.norm
  have hprod : Integrable
      (fun p : Plane × Plane => heatKernel2 θ p.1 * ‖U p.2‖)
      ((volume : Measure Plane).prod (cellμ c)) := hkernel.mul_prod hUnorm
  have hdom : Integrable
      (fun p : Plane × Plane => M * (heatKernel2 θ p.1 * ‖U p.2‖))
      ((volume : Measure Plane).prod (cellμ c)) := by
    simpa only [mul_comm] using hprod.const_mul M
  have hmeasT : Measurable T := hT.smooth.continuous.measurable
  have hmeasU : Measurable U := hU.smooth.continuous.measurable
  have hmeasK : Measurable (heatKernel2 θ) :=
    UnforcedLeray.B0284.measurable_heatKernel2_right θ
  have hjoint : Measurable (fun p : Plane × Plane =>
      heatKernel2 θ p.1 * ⟪T (p.2 - p.1), U p.2⟫_ℝ) := by
    fun_prop
  refine hdom.mono' hjoint.aestronglyMeasurable ?_
  filter_upwards with p
  have hk : 0 ≤ heatKernel2 θ p.1 :=
    UnforcedLeray.B0284.heatKernel2_nonneg hθ p.1
  have hTnorm : ‖T (p.2 - p.1)‖ ≤ M := hTbound _
  have hinner : |⟪T (p.2 - p.1), U p.2⟫_ℝ| ≤
      ‖T (p.2 - p.1)‖ * ‖U p.2‖ := abs_real_inner_le_norm _ _
  have hnonneg : 0 ≤ M * (heatKernel2 θ p.1 * ‖U p.2‖) := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  calc
    heatKernel2 θ p.1 * |⟪T (p.2 - p.1), U p.2⟫_ℝ| ≤
        heatKernel2 θ p.1 * (‖T (p.2 - p.1)‖ * ‖U p.2‖) :=
        mul_le_mul_of_nonneg_left hinner hk
    _ ≤ heatKernel2 θ p.1 * (M * ‖U p.2‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg (U p.2))) hk
    _ = M * (heatKernel2 θ p.1 * ‖U p.2‖) := by ring

/-- Fubini swaps the Gaussian shift and the centered-cell integration for the actual smooth
pairing integrand. -/
theorem integral_integral_heatVecGaussianPairing_swap {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T U : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hU : UnforcedLeray.Sob.IsCylSmooth c U) :
    (∫ w : Plane, (∫ z : Plane,
      heatKernel2 θ w * ⟪T (z - w), U z⟫_ℝ ∂(cellμ c)) ∂(volume : Measure Plane)) =
    (∫ z : Plane, (∫ w : Plane,
      heatKernel2 θ w * ⟪T (z - w), U z⟫_ℝ ∂(volume : Measure Plane)) ∂(cellμ c)) := by
  exact integral_integral_swap
    (integrable_heatVecGaussianPairingProduct hc hθ hT hU)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.integrable_heatVecGaussianPairingProduct
