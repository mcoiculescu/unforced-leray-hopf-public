import UnforcedLeray.Analysis.LerayProjection.Mollifier.Basic
import UnforcedLeray.Analysis.LerayProjection.TranslationH1

/-!
# Strong mollification in the actual H¹ Hilbert graph

A normalized compact average of H¹ translations is a genuine Bochner integral
in the complete weak Sobolev graph. Its value and each derivative are exactly
the corresponding L² averages. Strong convergence is therefore in the full
Sobolev norm, rather than only in the field component.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff Convolution
open UnforcedLeray.SobolevGraph

namespace UnforcedLeray.Leray

/-- The normalized compact average taken in the complete actual H¹ graph. -/
def h1MollifierAverage (φ : ContDiffBump (0 : Space)) (F : H1) : H1 :=
  ∫ y : Space, φ.normed volume y • h1Translation (-y) F

/-- Strong continuity and compact support justify this H¹-valued integral. -/
theorem h1MollifierAverage_integrable (φ : ContDiffBump (0 : Space)) (F : H1) :
    Integrable (fun y : Space => φ.normed volume y • h1Translation (-y) F) volume := by
  have hc : Continuous (fun y : Space => φ.normed volume y • h1Translation (-y) F) :=
    (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous.smul
      ((continuous_h1Translation_orbit F).comp continuous_neg)
  exact hc.integrable_of_hasCompactSupport φ.hasCompactSupport_normed.smul_right

/-- The average's field component is exactly the L² translation average. -/
@[simp] theorem value_h1MollifierAverage (φ : ContDiffBump (0 : Space)) (F : H1) :
    (h1MollifierAverage φ F).value = mollifierAverage φ F.value := by
  change H1.valueCLM (∫ y : Space, φ.normed volume y • h1Translation (-y) F) = _
  rw [← H1.valueCLM.integral_comp_comm (h1MollifierAverage_integrable φ F)]
  simp only [map_smul, H1.valueCLM_apply, value_h1Translation, mollifierAverage]

/-- Each actual weak derivative is averaged by the same L² mollifier. -/
@[simp] theorem derivative_h1MollifierAverage (φ : ContDiffBump (0 : Space))
    (F : H1) (i : Fin 3) :
    (h1MollifierAverage φ F).derivative i = mollifierAverage φ (F.derivative i) := by
  change H1.derivativeCLM i (∫ y : Space, φ.normed volume y • h1Translation (-y) F) = _
  rw [← (H1.derivativeCLM i).integral_comp_comm (h1MollifierAverage_integrable φ F)]
  simp only [map_smul, H1.derivativeCLM_apply, derivative_h1Translation, mollifierAverage]

/-- This actual smoothing operator contracts the full H¹ graph norm. -/
theorem norm_h1MollifierAverage_le (φ : ContDiffBump (0 : Space)) (F : H1) :
    ‖h1MollifierAverage φ F‖ ≤ ‖F‖ := by
  calc
    ‖h1MollifierAverage φ F‖ ≤
        ∫ y : Space, ‖φ.normed volume y • h1Translation (-y) F‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : Space, φ.normed volume y * ‖F‖ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed y), norm_h1Translation]
    _ = ‖F‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- Shrinking normalized bumps converge in the actual H¹ norm. -/
theorem h1MollifierAverage_tendsto (F : H1) :
    Tendsto (fun n => h1MollifierAverage (SobolevEmbedding.shrinkingMollifier n) F)
      atTop (𝓝 F) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure Space)) SobolevEmbedding.shrinkingMollifier_rOut_tendsto
    (continuous_h1Translation_orbit F) (0 : Space)
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub,
    h1Translation_zero, h1MollifierAverage] using h

end UnforcedLeray.Leray
