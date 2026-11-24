import UnforcedLeray.Lib.HeatCylinder.HeatVecDerivative
import UnforcedLeray.Lib.HeatCylinder.SmoothCLM

/-!
# Ordinary heat derivative commutation from actual global bounds

Gaussian differentiation does not require compact axial support. Explicit global field and
Fréchet-derivative bounds suffice, as for the actual Gaussian-tailed train datum.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (heatKernel2)

/-- Coordinate directional derivatives control the operator norm of a derivative on the product
plane with its max norm. -/
theorem norm_fderiv_plane_le_coordinate_directions {T : Plane → Vec} (z : Plane) :
    ‖fderiv ℝ T z‖ ≤ ‖fderiv ℝ T z (1, 0)‖ + ‖fderiv ℝ T z (0, 1)‖ := by
  let L := fderiv ℝ T z
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv : v = v.1 • ((1, 0) : Plane) + v.2 • ((0, 1) : Plane) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  calc
    ‖v.1 • L (1, 0) + v.2 • L (0, 1)‖ ≤
        ‖v.1 • L (1, 0)‖ + ‖v.2 • L (0, 1)‖ := norm_add_le _ _
    _ = ‖v.1‖ * ‖L (1, 0)‖ + ‖v.2‖ * ‖L (0, 1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖v‖ * ‖L (1, 0)‖ + ‖v‖ * ‖L (0, 1)‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (norm_fst_le v) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (norm_snd_le v) (norm_nonneg _))
    _ = (‖L (1, 0)‖ + ‖L (0, 1)‖) * ‖v‖ := by ring
    _ = (‖fderiv ℝ T z (1, 0)‖ + ‖fderiv ℝ T z (0, 1)‖) * ‖v‖ := by rfl
    _ ≤ (‖fderiv ℝ T z (1, 0)‖ + ‖fderiv ℝ T z (0, 1)‖) *
        ‖v.1 • ((1, 0) : Plane) + v.2 • ((0, 1) : Plane)‖ := by rw [← hv]

/-- Fréchet differentiation of actual vector heat evaluated in a direction, under explicit global
bounds on the input and its derivative. -/
theorem fderiv_heatVecConvolution_apply_of_bounds {θ : ℝ} (hθ : 0 < θ)
    {T : Plane → Vec} (hT : ContDiff ℝ 1 T)
    {M₀ M₁ : ℝ} (hTbound : ∀ x, ‖T x‖ ≤ M₀)
    (hderivBound : ∀ x, ‖fderiv ℝ T x‖ ≤ M₁)
    (z e : Plane) :
    fderiv ℝ (heatVecConvolution θ T) z e =
      heatVecConvolution θ (fun x => fderiv ℝ T x e) z := by
  have hfd := hasFDerivAt_heatVecConvolution hθ hT hTbound hderivBound z
  let J : Plane → Plane →L[ℝ] Vec := fun w =>
    (heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))
  have hkernel : Integrable (heatKernel2 θ) := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hJmeas : AEStronglyMeasurable J volume := by
    have hder : Continuous (fun w : Plane => fderiv ℝ T (z - w)) :=
      (hT.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)
    have hheatKernel : Continuous (heatKernel2 θ) := by
      unfold UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
      fun_prop
    have hker : Continuous (heatVecKernelCLM θ) := by
      unfold heatVecKernelCLM
      exact hheatKernel.smul continuous_const
    exact (hker.clm_comp hder).measurable.aestronglyMeasurable
  have hJbound : ∀ᵐ w ∂(volume : Measure Plane),
      ‖J w‖ ≤ heatKernel2 θ w * M₁ := by
    filter_upwards [] with w
    calc
      ‖(heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))‖ ≤
          ‖heatVecKernelCLM θ w‖ * ‖fderiv ℝ T (z - w)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ heatKernel2 θ w * M₁ :=
        mul_le_mul (norm_heatVecKernelCLM_le hθ w) (hderivBound (z - w))
          (norm_nonneg _) (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)
  have hJint : Integrable J volume :=
    (hkernel.mul_const M₁).mono' hJmeas hJbound
  have hEval :
      (∫ w : Plane, (heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))) e =
        ∫ w : Plane, heatKernel2 θ w • fderiv ℝ T (z - w) e := by
    calc
      (∫ w : Plane, (heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))) e =
          ∫ w : Plane, ((heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))) e :=
        ContinuousLinearMap.integral_apply hJint e
      _ = ∫ w : Plane, heatKernel2 θ w • fderiv ℝ T (z - w) e := by
        congr 1
  rw [hfd.fderiv, hEval]
  rfl

/-- Every ordered derivative word commutes with actual Gaussian heat for a smooth field whenever
its derivatives and their Fréchet derivatives have global bounds. -/
theorem iterD_heatVecConvolution_commute_of_bounds {θ : ℝ} (hθ : 0 < θ)
    {T : Plane → Vec} (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hfieldBounds : ∀ vs : List Plane, ∃ M : ℝ, ∀ z,
      ‖UnforcedLeray.Sob.iterD vs T z‖ ≤ M)
    (hderivBounds : ∀ vs : List Plane, ∃ M : ℝ, ∀ z,
      ‖fderiv ℝ (UnforcedLeray.Sob.iterD vs T) z‖ ≤ M)
    (vs : List Plane) :
    UnforcedLeray.Sob.iterD vs (heatVecConvolution θ T) =
      heatVecConvolution θ (UnforcedLeray.Sob.iterD vs T) := by
  induction vs with
  | nil => rfl
  | cons e vs ih =>
      funext z
      change fderiv ℝ (UnforcedLeray.Sob.iterD vs
        (heatVecConvolution θ T)) z e =
        heatVecConvolution θ (UnforcedLeray.Sob.iterD (e :: vs) T) z
      rw [ih]
      obtain ⟨M₀, hM₀⟩ := hfieldBounds vs
      obtain ⟨M₁, hM₁⟩ := hderivBounds vs
      rw [fderiv_heatVecConvolution_apply_of_bounds hθ
        ((UnforcedLeray.Sob.contDiff_iterD hT vs).of_le (by norm_num))
        hM₀ hM₁ z e]
      rfl

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.norm_fderiv_plane_le_coordinate_directions
#print axioms UnforcedLeray.HeatCylinder.fderiv_heatVecConvolution_apply_of_bounds
#print axioms UnforcedLeray.HeatCylinder.iterD_heatVecConvolution_commute_of_bounds
