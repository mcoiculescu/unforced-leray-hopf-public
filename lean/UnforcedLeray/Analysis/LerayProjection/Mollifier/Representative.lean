import UnforcedLeray.Analysis.LerayProjection.Mollifier.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Representatives of the L²-valued mollifier average

The Bochner average of translated L² classes is the class of the usual
pointwise convolution. Every interchange of integrals is justified: the
scalar pairing integrand is dominated by the normalized kernel times the
sum of two squared L² norms.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Convolution Topology

namespace UnforcedLeray.Leray

/-- Product integrability needed to identify actual convolution with the L² average. -/
theorem mollifier_pairing_integrable (φ : ContDiffBump (0 : Space)) (F G : L2Space) :
    Integrable (fun p : Space × Space => φ.normed volume p.2 *
      inner ℝ (G p.1) (F (p.1 - p.2))) (volume.prod volume) := by
  have hF : Integrable (fun x : Space => ‖F x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  have hG : Integrable (fun x : Space => ‖G x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable G)).mp (Lp.memLp G)
  have hfirst : Integrable (fun p : Space × Space =>
      ‖φ.normed volume p.2‖ * ‖G p.1‖ ^ 2) (volume.prod volume) := by
    simpa only [mul_comm] using hG.mul_prod φ.integrable_normed.norm
  have hsecond : Integrable (fun p : Space × Space =>
      ‖φ.normed volume p.2‖ * ‖F (p.1 - p.2)‖ ^ 2) (volume.prod volume) := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      φ.integrable_normed.norm.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hF
  have hm : StronglyMeasurable (fun p : Space × Space => φ.normed volume p.2 *
      inner ℝ (G p.1) (F (p.1 - p.2))) := by
    exact ((φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous.comp continuous_snd).stronglyMeasurable.mul
      (((Lp.stronglyMeasurable G).comp_measurable measurable_fst).inner
        ((Lp.stronglyMeasurable F).comp_measurable continuous_sub.measurable))
  refine (hfirst.add hsecond).mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  rw [norm_mul]
  calc
    ‖φ.normed volume p.2‖ * ‖inner ℝ (G p.1) (F (p.1 - p.2))‖
        ≤ ‖φ.normed volume p.2‖ * (‖G p.1‖ * ‖F (p.1 - p.2)‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
    _ ≤ ‖φ.normed volume p.2‖ * (‖G p.1‖ ^ 2 + ‖F (p.1 - p.2)‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      nlinarith [sq_nonneg (‖G p.1‖ - ‖F (p.1 - p.2)‖)]
    _ = _ := mul_add _ _ _

/-- Pairing a pointwise convolution equals the iterated pairing with translations. -/
theorem integral_inner_mollification (φ : ContDiffBump (0 : Space)) (F G : L2Space) :
    (∫ x : Space, inner ℝ (G x) (SobolevEmbedding.mollification φ (F : SpatialField) x)) =
      ∫ y : Space, φ.normed volume y * inner ℝ G (translation (-y) F) := by
  calc
    _ = ∫ x : Space, ∫ y : Space,
        φ.normed volume y * inner ℝ (G x) (F (x - y)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [SobolevEmbedding.mollification, convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply]
      rw [← integral_inner
        (SobolevEmbedding.mollification_integrable φ (F : SpatialField) (Lp.memLp F) x) (G x)]
      simp only [real_inner_smul_right]
    _ = ∫ y : Space, ∫ x : Space,
        φ.normed volume y * inner ℝ (G x) (F (x - y)) :=
      integral_integral_swap (mollifier_pairing_integrable φ F G)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_const_mul, L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [coeFn_translation (-y) F] with x hx
      simp only [sub_eq_add_neg, hx]

/-- The L²-valued Bochner average is the class of the actual pointwise mollification. -/
theorem mollifierAverage_eq_toL2 (φ : ContDiffBump (0 : Space)) (F : L2Space) :
    mollifierAverage φ F = toL2 (SobolevEmbedding.mollification φ (F : SpatialField)) := by
  apply ext_inner_left ℝ
  intro G
  have hm := SobolevEmbedding.mollification_memLp φ (F : SpatialField) (Lp.memLp F)
  calc
    inner ℝ G (mollifierAverage φ F) =
        ∫ y : Space, φ.normed volume y * inner ℝ G (translation (-y) F) := by
      rw [mollifierAverage, ← integral_inner (mollifierAverage_integrable φ F) G]
      simp only [real_inner_smul_right]
    _ = ∫ x : Space, inner ℝ (G x) (SobolevEmbedding.mollification φ (F : SpatialField) x) :=
      (integral_inner_mollification φ F G).symm
    _ = inner ℝ G (toL2 (SobolevEmbedding.mollification φ (F : SpatialField))) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [coeFn_toL2 hm] with x hx
      rw [hx]

/-- In particular the representative of the average is the ordinary convolution almost everywhere. -/
theorem coeFn_mollifierAverage (φ : ContDiffBump (0 : Space)) (F : L2Space) :
    (mollifierAverage φ F : SpatialField) =ᵐ[volume]
      SobolevEmbedding.mollification φ (F : SpatialField) := by
  rw [mollifierAverage_eq_toL2]
  exact coeFn_toL2 (SobolevEmbedding.mollification_memLp φ (F : SpatialField) (Lp.memLp F))

/-- The actual convolution depends only on the a.e. class of the input field. -/
theorem mollification_congr_ae (φ : ContDiffBump (0 : Space))
    {f g : SpatialField} (hfg : f =ᵐ[volume] g) :
    SobolevEmbedding.mollification φ f = SobolevEmbedding.mollification φ g :=
  convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (EventuallyEq.refl _ _) hfg

/-- The quotient/pointwise bridge for every genuinely square-integrable field. -/
theorem mollifierAverage_toL2 (φ : ContDiffBump (0 : Space))
    {f : SpatialField} (hf : MemLp f 2 volume) :
    mollifierAverage φ (toL2 f) = toL2 (SobolevEmbedding.mollification φ f) := by
  rw [mollifierAverage_eq_toL2, mollification_congr_ae φ (coeFn_toL2 hf)]

/-- Actual mollifications by compact smooth kernels converge strongly in L² to every L² field. -/
theorem mollification_toL2_tendsto {f : SpatialField} (hf : MemLp f 2 volume) :
    Tendsto (fun n => toL2 (SobolevEmbedding.mollification
      (SobolevEmbedding.shrinkingMollifier n) f)) atTop (𝓝 (toL2 f)) := by
  simpa only [mollifierAverage_toL2 _ hf] using mollifierAverage_tendsto (toL2 f)

end UnforcedLeray.Leray
