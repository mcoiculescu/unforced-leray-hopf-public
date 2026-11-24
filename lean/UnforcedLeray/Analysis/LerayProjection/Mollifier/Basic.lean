import UnforcedLeray.Analysis.LerayProjection.TranslationL2
import UnforcedLeray.Analysis.SobolevEmbedding.Density
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Compact mollification as an actual L²-valued Bochner average

The integral averages the genuine spatial translation operators. Compactness
of the scalar kernel and strong continuity of the translation orbit prove
Bochner integrability. Its L² contraction follows from this integral.
Shrinking normalized bumps converge
strongly in L² by the proved strong continuity, without a density assumption.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff Convolution

namespace UnforcedLeray.Leray

/-- The normalized compact bump average in the complete vector-valued L² space. -/
def mollifierAverage (φ : ContDiffBump (0 : Space)) (F : L2Space) : L2Space :=
  ∫ y : Space, φ.normed volume y • translation (-y) F

/-- The average is a genuine Bochner integral; it never uses nonintegrability fallback. -/
theorem mollifierAverage_integrable (φ : ContDiffBump (0 : Space)) (F : L2Space) :
    Integrable (fun y : Space => φ.normed volume y • translation (-y) F) volume := by
  have hc : Continuous (fun y : Space => φ.normed volume y • translation (-y) F) :=
    (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous.smul
      ((continuous_translation_orbit F).comp continuous_neg)
  exact hc.integrable_of_hasCompactSupport φ.hasCompactSupport_normed.smul_right

/-- Positivity and unit mass make the average an L² contraction. -/
theorem norm_mollifierAverage_le (φ : ContDiffBump (0 : Space)) (F : L2Space) :
    ‖mollifierAverage φ F‖ ≤ ‖F‖ := by
  calc
    ‖mollifierAverage φ F‖ ≤
        ∫ y : Space, ‖φ.normed volume y • translation (-y) F‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : Space, φ.normed volume y * ‖F‖ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed y), norm_translation]
    _ = ‖F‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

@[simp] theorem mollifierAverage_add (φ : ContDiffBump (0 : Space)) (F G : L2Space) :
    mollifierAverage φ (F + G) = mollifierAverage φ F + mollifierAverage φ G := by
  simp only [mollifierAverage, map_add, smul_add]
  exact integral_add (mollifierAverage_integrable φ F) (mollifierAverage_integrable φ G)

@[simp] theorem mollifierAverage_smul (φ : ContDiffBump (0 : Space)) (c : ℝ) (F : L2Space) :
    mollifierAverage φ (c • F) = c • mollifierAverage φ F := by
  simp only [mollifierAverage, map_smul, smul_comm (φ.normed volume _) c, integral_smul]

/-- Strong L² convergence for the concrete shrinking family used by the Sobolev proof. -/
theorem mollifierAverage_tendsto (F : L2Space) :
    Tendsto (fun n => mollifierAverage (SobolevEmbedding.shrinkingMollifier n) F)
      atTop (𝓝 F) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure Space)) SobolevEmbedding.shrinkingMollifier_rOut_tendsto
    (continuous_translation_orbit F) (0 : Space)
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub,
    translation_zero, mollifierAverage] using h

end UnforcedLeray.Leray
