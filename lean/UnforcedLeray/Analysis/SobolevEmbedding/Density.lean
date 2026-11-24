import UnforcedLeray.Analysis.SobolevEmbedding.MollifierL2
import UnforcedLeray.Analysis.SobolevEmbedding.Smooth
import UnforcedLeray.Analysis.WeakDerivative
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Whole-space Sobolev inequality for actual weak H¹ fields

Compact mollification is smooth, its classical derivatives are convolutions
of the given weak derivatives, and it contracts the L² norm. A shrinking
family converges almost everywhere by Lebesgue differentiation. Fatou then
passes the proved smooth R³ Sobolev inequality to every genuine weak H¹ field.
No smooth-density or Sobolev estimate is assumed in the weak theorem.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Convolution Topology ENNReal
namespace UnforcedLeray.SobolevEmbedding

theorem translated_mollifier_test (φ : ContDiffBump (0:Space)) (x : Space) :
    IsSpatialTest (fun y : Space => φ.normed volume (x-y)) := by
  constructor
  · exact φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  · exact φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)

theorem translated_mollifier_test_derivative (φ : ContDiffBump (0:Space)) (x y : Space) (i : Fin 3) :
    spatialTestDerivative i (fun z : Space => φ.normed volume (x-z)) y =
      - spatialTestDerivative i (φ.normed volume) (x-y) := by
  have hd := ((φ.contDiff_normed (μ := (volume : Measure Space)) (n := 1)).differentiable
    (by norm_num) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  change (fderiv ℝ (φ.normed volume ∘ (fun z : Space => x-z)) y) (coordinateVector i) = _
  rw [hd.fderiv]
  simp [spatialTestDerivative]

lemma mollification_derivative {f g : SpatialField} {i : Fin 3}
    (h : HasWeakSpatialDerivative i f g) (hf : MemLp f 2 volume)
    (φ : ContDiffBump (0:Space)) (x : Space) :
    fderiv ℝ (mollification φ f) x (coordinateVector i) =
      mollification φ g x := by
  have hid := h.identity (fun y : Space => φ.normed volume (x-y)) (translated_mollifier_test φ x)
  simp_rw [translated_mollifier_test_derivative, neg_smul] at hid
  rw [integral_neg] at hid
  have hd := (φ.hasCompactSupport_normed (μ := (volume : Measure Space))).hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip (hf.locallyIntegrable (by norm_num))
    (φ.contDiff_normed (n := 1)) x
  rw [mollification, ← convolution_flip, hd.fderiv,
    convolution_precompR_apply _ (hf.locallyIntegrable (by norm_num))
      ((φ.hasCompactSupport_normed (μ := (volume : Measure Space))).fderiv ℝ)
      ((φ.contDiff_normed (n := 1)).continuous_fderiv (by norm_num))]
  change (∫ y : Space, spatialTestDerivative i (φ.normed volume) (x-y) • f y) = _
  rw [mollification, convolution_eq_swap]
  exact neg_injective hid

/-- One explicit family of normalized smooth compact mollifiers. -/
def shrinkingMollifier (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

theorem shrinkingMollifier_rOut_tendsto :
    Tendsto (fun n => (shrinkingMollifier n).rOut) atTop (𝓝 (0 : ℝ)) := by
  simpa [shrinkingMollifier, div_eq_mul_inv] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

theorem shrinkingMollifier_shape (n : ℕ) :
    (shrinkingMollifier n).rOut ≤ 2 * (shrinkingMollifier n).rIn := by
  dsimp [shrinkingMollifier]
  simp [div_eq_mul_inv]

/-- These actual smooth convolutions recover every L² field almost everywhere. -/
theorem mollification_ae_tendsto (f : SpatialField) (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, Tendsto (fun n => mollification (shrinkingMollifier n) f x)
      atTop (𝓝 (f x)) :=
  ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    shrinkingMollifier_rOut_tendsto
    (Eventually.of_forall shrinkingMollifier_shape)
    (hf.locallyIntegrable (by norm_num))

/-- The homogeneous Sobolev inequality for a genuine L² field with three L²
weak derivatives. The estimate is obtained by mollification and Fatou. -/
theorem weak_eLpNorm_six_le_sum {f : SpatialField} {g : Fin 3 → SpatialField}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) :
    eLpNorm f 6 volume ≤ (sobolevConstant : ℝ≥0∞) *
      ∑ i : Fin 3, eLpNorm (g i) 2 volume := by
  have hbound (n : ℕ) :
      eLpNorm (mollification (shrinkingMollifier n) f) 6 volume ≤
        (sobolevConstant : ℝ≥0∞) * ∑ i : Fin 3, eLpNorm (g i) 2 volume := by
    have hs := smooth_eLpNorm_six_le_sum_coordinates
      ((mollification_smooth (shrinkingMollifier n) f hf).of_le (by simp))
      (mollification_memLp (shrinkingMollifier n) f hf)
    apply hs.trans
    refine mul_le_mul le_rfl ?_ zero_le zero_le
    apply Finset.sum_le_sum
    intro i _
    have he : (fun x => fderiv ℝ (mollification (shrinkingMollifier n) f) x
        (coordinateVector i)) = mollification (shrinkingMollifier n) (g i) := by
      funext x
      exact mollification_derivative (hderiv i) hf (shrinkingMollifier n) x
    rw [he]
    exact mollification_eLpNorm_le (shrinkingMollifier n) (g i) (hg i)
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm
    (p := 6) (fun n => (mollification_smooth (shrinkingMollifier n) f hf).continuous.aestronglyMeasurable)
    f (mollification_ae_tendsto f hf)
  exact hfatou.trans (liminf_le_of_frequently_le (Eventually.of_forall hbound).frequently)

/-- Every actual weak H¹ field on R³ belongs to L⁶. -/
theorem weak_memLp_six {f : SpatialField} {g : Fin 3 → SpatialField}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) : MemLp f 6 volume := by
  refine ⟨hf.aestronglyMeasurable, (weak_eLpNorm_six_le_sum hf hg hderiv).trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.sum_lt_top.mpr (fun i _ => (hg i).2))

/-- Finite real-valued homogeneous Sobolev bound for weak H¹ fields. -/
theorem weak_l6Norm_le_sum {f : SpatialField} {g : Fin 3 → SpatialField}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) :
    (eLpNorm f 6 volume).toReal ≤ (sobolevConstant : ℝ) *
      ∑ i : Fin 3, l2Norm (g i) := by
  have hs : (∑ i : Fin 3, eLpNorm (g i) 2 volume) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr (fun i _ => (hg i).2)).ne
  have hc : (sobolevConstant : ℝ≥0∞) * ∑ i : Fin 3, eLpNorm (g i) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hs
  have h := ENNReal.toReal_mono hc (weak_eLpNorm_six_le_sum hf hg hderiv)
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_sum (fun i _ => (hg i).2.ne), l2Norm] using h

end UnforcedLeray.SobolevEmbedding
