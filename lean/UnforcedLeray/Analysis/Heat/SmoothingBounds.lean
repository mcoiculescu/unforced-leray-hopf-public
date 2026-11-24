import UnforcedLeray.Analysis.Heat.SobolevSmoothing
import UnforcedLeray.Analysis.Heat.KernelSmoothingBounds

/-!
# Quantitative L²-to-H¹/H² heat smoothing

The norms below are bounded using the literal first and second Gaussian
kernel masses. Every derivative is the genuine weak derivative already
established in SobolevSmoothing; no regularity assumption is made on the L²
input. The Sobolev bounds use the exact square-sum graph norms.
-/

noncomputable section
open MeasureTheory
namespace UnforcedLeray.Heat

/-- The actual heat convolution contracts the vector L² norm. -/
theorem norm_heatConvolution_le {t : ℝ} (ht : 0 < t) (F : L2Space) :
    ‖convolutionOperator (kernel t) (kernel_integrable ht) F‖ ≤ ‖F‖ := by
  have h := convolutionToL2_norm_le (kernel t) (kernel_integrable ht) F
  have he : (∫ x : Space, ‖kernel t x‖) = 1 := by
    simp_rw [Real.norm_of_nonneg (kernel_nonneg ht _)]
    exact integral_kernel ht
  rw [convolutionOperator_apply]
  simpa only [he, one_mul] using h

/-- First spatial derivatives have the required inverse-square-root time bound. -/
theorem norm_firstDerivativeOperator_le {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    ‖firstDerivativeOperator ht i‖ ≤ firstSmoothingConstant * t ^ (-(1 : ℝ) / 2) :=
  (convolutionOperator_norm_le _ _).trans (firstDerivativeKernel_L1_scale_bound ht i)

/-- Ordered second derivatives have the required inverse-time bound. -/
theorem norm_secondDerivativeOperator_le {t : ℝ} (ht : 0 < t) (i j : Fin 3) :
    ‖secondDerivativeOperator ht i j‖ ≤ secondSmoothingConstant * t⁻¹ :=
  (convolutionOperator_norm_le _ _).trans (secondDerivativeKernel_L1_scale_bound ht i j)

theorem norm_firstDerivativeOperator_apply_le {t : ℝ} (ht : 0 < t)
    (i : Fin 3) (F : L2Space) :
    ‖firstDerivativeOperator ht i F‖ ≤
      (firstSmoothingConstant * t ^ (-(1 : ℝ) / 2)) * ‖F‖ :=
  ((firstDerivativeOperator ht i).le_opNorm F).trans
    (mul_le_mul_of_nonneg_right (norm_firstDerivativeOperator_le ht i) (norm_nonneg _))

theorem norm_secondDerivativeOperator_apply_le {t : ℝ} (ht : 0 < t)
    (i j : Fin 3) (F : L2Space) :
    ‖secondDerivativeOperator ht i j F‖ ≤
      (secondSmoothingConstant * t⁻¹) * ‖F‖ :=
  ((secondDerivativeOperator ht i j).le_opNorm F).trans
    (mul_le_mul_of_nonneg_right (norm_secondDerivativeOperator_le ht i j) (norm_nonneg _))

/-- The finite square-sum factor for the actual H¹ graph norm. -/
def h1SmoothingBound (t : ℝ) : ℝ :=
  Real.sqrt (1 + 3 * (firstSmoothingConstant * t ^ (-(1 : ℝ) / 2)) ^ 2)

/-- The thirteen-component factor for the actual H² graph norm. -/
def h2SmoothingBound (t : ℝ) : ℝ :=
  Real.sqrt (1 + 3 * (firstSmoothingConstant * t ^ (-(1 : ℝ) / 2)) ^ 2 +
    9 * (secondSmoothingConstant * t⁻¹) ^ 2)

theorem norm_heatToH1_apply_le {t : ℝ} (ht : 0 < t) (F : L2Space) :
    ‖heatToH1 ht F‖ ≤ h1SmoothingBound t * ‖F‖ := by
  let A := firstSmoothingConstant * t ^ (-(1 : ℝ) / 2)
  have hA : 0 ≤ A := mul_nonneg firstSmoothingConstant_pos.le (Real.rpow_nonneg ht.le _)
  have hbase : ‖convolutionOperator (kernel t) (kernel_integrable ht) F‖ ^ 2 ≤ ‖F‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_heatConvolution_le ht F)
  have hfirst : ∀ i : Fin 3, ‖firstDerivativeOperator ht i F‖ ^ 2 ≤ (A * ‖F‖) ^ 2 :=
    fun i => (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA (norm_nonneg _))).mpr
      (norm_firstDerivativeOperator_apply_le ht i F)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  calc
    ‖heatToH1 ht F‖ ^ 2 =
        ‖convolutionOperator (kernel t) (kernel_integrable ht) F‖ ^ 2 +
          ∑ i : Fin 3, ‖firstDerivativeOperator ht i F‖ ^ 2 := by
      rw [SobolevGraph.H1.norm_sq]
      simp only [heatToH1_value, heatToH1_derivative]
    _ ≤ ‖F‖ ^ 2 + ∑ i : Fin 3, (A * ‖F‖) ^ 2 :=
      add_le_add hbase (Finset.sum_le_sum (fun i _ => hfirst i))
    _ = (h1SmoothingBound t * ‖F‖) ^ 2 := by
      rw [h1SmoothingBound]
      simp only [mul_pow]
      rw [Real.sq_sqrt (by positivity)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]
      dsimp [A]
      ring

theorem norm_heatToH2_apply_le {t : ℝ} (ht : 0 < t) (F : L2Space) :
    ‖heatToH2 ht F‖ ≤ h2SmoothingBound t * ‖F‖ := by
  let A := firstSmoothingConstant * t ^ (-(1 : ℝ) / 2)
  let B := secondSmoothingConstant * t⁻¹
  have hA : 0 ≤ A := mul_nonneg firstSmoothingConstant_pos.le (Real.rpow_nonneg ht.le _)
  have hB : 0 ≤ B := mul_nonneg secondSmoothingConstant_pos.le (inv_nonneg.mpr ht.le)
  have hbase : ‖convolutionOperator (kernel t) (kernel_integrable ht) F‖ ^ 2 ≤ ‖F‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_heatConvolution_le ht F)
  have hfirst : ∀ i : Fin 3, ‖firstDerivativeOperator ht i F‖ ^ 2 ≤ (A * ‖F‖) ^ 2 :=
    fun i => (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA (norm_nonneg _))).mpr
      (norm_firstDerivativeOperator_apply_le ht i F)
  have hsecond : ∀ i j : Fin 3, ‖secondDerivativeOperator ht i j F‖ ^ 2 ≤ (B * ‖F‖) ^ 2 :=
    fun i j => (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr
      (norm_secondDerivativeOperator_apply_le ht i j F)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  calc
    ‖heatToH2 ht F‖ ^ 2 =
        ‖convolutionOperator (kernel t) (kernel_integrable ht) F‖ ^ 2 +
          (∑ i : Fin 3, ‖firstDerivativeOperator ht i F‖ ^ 2) +
          ∑ i : Fin 3, ∑ j : Fin 3, ‖secondDerivativeOperator ht i j F‖ ^ 2 := by
      rw [SobolevGraph.H2.norm_sq]
      simp only [heatToH2_value, heatToH2_first, heatToH2_second]
    _ ≤ ‖F‖ ^ 2 + (∑ i : Fin 3, (A * ‖F‖) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (B * ‖F‖) ^ 2 :=
      add_le_add (add_le_add hbase (Finset.sum_le_sum (fun i _ => hfirst i)))
        (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hsecond i j)))
    _ = (h2SmoothingBound t * ‖F‖) ^ 2 := by
      rw [h2SmoothingBound]
      simp only [mul_pow]
      rw [Real.sq_sqrt (by positivity)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]
      dsimp [A, B]
      ring

/-- Bounded smoothing into the actual H¹ Hilbert graph. -/
theorem norm_heatToH1_le {t : ℝ} (ht : 0 < t) : ‖heatToH1 ht‖ ≤ h1SmoothingBound t := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact norm_heatToH1_apply_le ht

/-- Bounded smoothing into the actual H² Hilbert graph. -/
theorem norm_heatToH2_le {t : ℝ} (ht : 0 < t) : ‖heatToH2 ht‖ ≤ h2SmoothingBound t := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact norm_heatToH2_apply_le ht

end UnforcedLeray.Heat
