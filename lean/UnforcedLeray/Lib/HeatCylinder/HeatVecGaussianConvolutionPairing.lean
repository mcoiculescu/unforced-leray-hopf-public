import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianShiftPairing
import UnforcedLeray.Lib.HeatCylinder.HeatVecConvolution

/-!
# Gaussian convolution and translation-average pairings

For smooth compact-axial periodic inputs and tests, the actual convolution pairing is the
Bochner Gaussian average of actual centered-cell translation pairings. The proof uses the
compiled joint-integrability and cell-Fubini results, without assuming an identification of the
two quotient-valued operators.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (cellμ L2v)
open UnforcedLeray.B0284 (heatKernel2)

/-- The real inner product with a fixed vector commutes with the actual Gaussian convolution
integral. -/
theorem inner_heatVecConvolution_eq_integral {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (z : Plane) (y : Vec) :
    ⟪heatVecConvolution θ T z, y⟫_ℝ =
      ∫ w : Plane, heatKernel2 θ w *
        ⟪T (z - w), y⟫_ℝ := by
  obtain ⟨M, hM, hTbound⟩ := exists_global_bound_of_cylSmooth hc hT
  have hkernel : Integrable (heatKernel2 θ) :=
    UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hdom : Integrable (fun w : Plane => M * heatKernel2 θ w) := by
    simpa only [mul_comm] using hkernel.const_mul M
  have hTarg : Measurable (fun w : Plane => T (z - w)) := by
    exact hT.smooth.continuous.measurable.comp (measurable_const.sub measurable_id)
  have hvecmeas : AEStronglyMeasurable
      (fun w : Plane => heatKernel2 θ w • T (z - w)) volume :=
    (UnforcedLeray.B0284.measurable_heatKernel2_right θ).aestronglyMeasurable.smul
      hTarg.aestronglyMeasurable
  have hvec : Integrable (fun w : Plane => heatKernel2 θ w • T (z - w)) volume := by
    refine hdom.mono' hvecmeas ?_
    filter_upwards with w
    have hk := UnforcedLeray.B0284.heatKernel2_nonneg hθ w
    rw [norm_smul, Real.norm_of_nonneg hk]
    calc
      heatKernel2 θ w * ‖T (z - w)‖ ≤ heatKernel2 θ w * M :=
        mul_le_mul_of_nonneg_left (hTbound _) hk
      _ = M * heatKernel2 θ w := by ring
  rw [heatVecConvolution]
  calc
    ⟪∫ w : Plane, heatKernel2 θ w • T (z - w), y⟫_ℝ =
        ⟪y, ∫ w : Plane, heatKernel2 θ w • T (z - w)⟫_ℝ := real_inner_comm _ _
    _ = ∫ w : Plane,
        ⟪y, heatKernel2 θ w • T (z - w)⟫_ℝ :=
          (integral_inner hvec y).symm
    _ = ∫ w : Plane, heatKernel2 θ w *
        ⟪T (z - w), y⟫_ℝ := by
          apply integral_congr_ae
          filter_upwards with w
          simp only [inner_smul_right, real_inner_comm]

/-- For smooth compact-axial periodic fields, the actual Gaussian convolution and the actual
centered translation average have identical scalar pairings on the cylinder cell. -/
theorem integral_heatVecConvolution_pairing_eq_centeredGaussianShiftAverageCLM
    {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T U : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hU : UnforcedLeray.Sob.IsCylSmooth c U)
    (hTm : MemLp T 2 (cellμ c)) (hUm : MemLp U 2 (cellμ c)) :
    (∫ z in UnforcedLeray.Cyl.cell c,
      ⟪heatVecConvolution θ T z, U z⟫_ℝ) =
      inner ℝ (centeredGaussianShiftAverageCLM hc hθ (hTm.toLp T)) (hUm.toLp U) := by
  have hconv :
      (∫ z in UnforcedLeray.Cyl.cell c, ⟪heatVecConvolution θ T z, U z⟫_ℝ) =
        ∫ z : Plane, (∫ w : Plane,
          heatKernel2 θ w * ⟪T (z - w), U z⟫_ℝ ∂(volume : Measure Plane)) ∂(cellμ c) := by
    apply integral_congr_ae
    filter_upwards with z
    exact inner_heatVecConvolution_eq_integral hc hθ hT z (U z)
  rw [hconv]
  calc
    (∫ z : Plane, (∫ w : Plane,
        heatKernel2 θ w * ⟪T (z - w), U z⟫_ℝ ∂(volume : Measure Plane)) ∂(cellμ c)) =
        ∫ w : Plane, (∫ z : Plane,
          heatKernel2 θ w * ⟪T (z - w), U z⟫_ℝ ∂(cellμ c)) ∂(volume : Measure Plane) :=
      (integral_integral_heatVecGaussianPairing_swap hc hθ hT hU).symm
    _ = ∫ w : Plane, heatKernel2 θ w *
        inner ℝ (planeShiftL2 hc w (hTm.toLp T)) (hUm.toLp U) := by
          apply integral_congr_ae
          filter_upwards with w
          rw [inner_planeShiftL2_smooth_eq_integral hc hT hTm hUm w]
          rw [integral_const_mul]
          simp only [cellμ]
    _ = inner ℝ (centeredGaussianShiftAverageCLM hc hθ (hTm.toLp T))
        (hUm.toLp U) := by
          rw [inner_centeredGaussianShiftAverageCLM]
          apply integral_congr_ae
          filter_upwards with w
          simp only [planeShiftL2CLM_apply]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.inner_heatVecConvolution_eq_integral
#print axioms UnforcedLeray.HeatCylinder.integral_heatVecConvolution_pairing_eq_centeredGaussianShiftAverageCLM
