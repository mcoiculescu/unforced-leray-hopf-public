import UnforcedLeray.Statement
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Actual compact mollification on R³

A normalized smooth compact bump acts on actual vector fields by convolution.
Its L² contraction is proved using Minkowski's integral inequality and
translation invariance of Lebesgue measure. No density or boundedness
certificate is assumed.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Convolution ENNReal

namespace UnforcedLeray.SobolevEmbedding

/-- Convolution with the normalized compact smooth bump. -/
def mollification (φ : ContDiffBump (0 : Space)) (f : SpatialField) : SpatialField :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

/-- Each value is a well-defined Bochner integral, from local integrability
and the compact support of the normalized bump. -/
theorem mollification_integrable (φ : ContDiffBump (0 : Space))
    (f : SpatialField) (hf : MemLp f 2 volume) (x : Space) :
    Integrable (fun y : Space => φ.normed volume y • f (x-y)) volume :=
  φ.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous
    (hf.locallyIntegrable (by norm_num)) x

/-- Every L² field has a genuinely smooth mollification. -/
theorem mollification_smooth (φ : ContDiffBump (0 : Space))
    (f : SpatialField) (hf : MemLp f 2 volume) :
    ContDiff ℝ ∞ (mollification φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed (hf.locallyIntegrable (by norm_num))

/-- A nonnegative scalar kernel of unit integral contracts vector-valued L². -/
theorem normalized_convolution_eLpNorm_le {k : Space → ℝ}
    (hk : Continuous k) (hki : Integrable k volume)
    (hkn : ∀ y, 0 ≤ k y) (hk1 : (∫ y, k y) = 1)
    (f : SpatialField) (hf : MemLp f 2 volume) :
    eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) 2 volume ≤
      eLpNorm f 2 volume := by
  have hF : AEStronglyMeasurable
      (fun p : Space × Space => k p.2 • f (p.1 - p.2)) (volume.prod volume) :=
    hk.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) hf.aestronglyMeasurable
  have hm := NonUniqueEuler.Conv.eLpNorm_integral_le
    (F := fun x y : Space => k y • f (x - y)) hF
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  have htranslate (y : Space) :
      eLpNorm (fun x : Space => f (x-y)) 2 volume = eLpNorm f 2 volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
        (measurePreserving_add_right (volume : Measure Space) (-y))
  have hnorm (y : Space) :
      eLpNorm (fun x : Space => k y • f (x-y)) 2 volume =
        ENNReal.ofReal (k y) * eLpNorm f 2 volume := by
    change eLpNorm ((k y) • (fun x : Space => f (x-y))) 2 volume = _
    rw [eLpNorm_const_smul, htranslate, Real.enorm_eq_ofReal (hkn y)]
  have hmass : (∫⁻ y : Space, ENNReal.ofReal (k y)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hki (Filter.Eventually.of_forall hkn), hk1]
    norm_num
  change eLpNorm (fun x : Space => ∫ y, k y • f (x-y)) 2 volume ≤ _
  calc
    _ ≤ ∫⁻ y : Space, eLpNorm (fun x : Space => k y • f (x-y)) 2 volume := hm
    _ = (∫⁻ y : Space, ENNReal.ofReal (k y)) * eLpNorm f 2 volume := by
      simp_rw [hnorm]
      exact lintegral_mul_const _ (ENNReal.continuous_ofReal.comp hk).measurable
    _ = _ := by rw [hmass, one_mul]

/-- The actual normalized bump convolution contracts the extended L² norm. -/
theorem mollification_eLpNorm_le (φ : ContDiffBump (0 : Space))
    (f : SpatialField) (hf : MemLp f 2 volume) :
    eLpNorm (mollification φ f) 2 volume ≤ eLpNorm f 2 volume :=
  normalized_convolution_eLpNorm_le
    (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous φ.integrable_normed
    (fun y => φ.nonneg_normed y) φ.integral_normed f hf

/-- Mollification preserves genuine square integrability. -/
theorem mollification_memLp (φ : ContDiffBump (0 : Space))
    (f : SpatialField) (hf : MemLp f 2 volume) :
    MemLp (mollification φ f) 2 volume :=
  ⟨(mollification_smooth φ f hf).continuous.aestronglyMeasurable,
    (mollification_eLpNorm_le φ f hf).trans_lt hf.2⟩

/-- The same contraction in the target statement's actual L² norm. -/
theorem mollification_l2Norm_le (φ : ContDiffBump (0 : Space))
    (f : SpatialField) (hf : MemLp f 2 volume) :
    l2Norm (mollification φ f) ≤ l2Norm f :=
  ENNReal.toReal_mono hf.2.ne (mollification_eLpNorm_le φ f hf)

end UnforcedLeray.SobolevEmbedding
