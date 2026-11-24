import UnforcedLeray.Analysis.LerayProjection.TranslationL2
import UnforcedLeray.Analysis.LerayProjection.TranslationWeakDerivative
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiating actual compact-test pairings along translation orbits

Pairing an L² field translated by `a` with a compact smooth scalar test equals
convolution with the reflected test at `a`. The convolution is an actual
integrable Bochner integral and is smooth. Its directional derivative therefore
computes the derivative of the translated test pairing without assuming any
weak derivative for the field. If the field has a genuine L² weak derivative,
the original weak identity identifies the derivative pairing with the translated
weak derivative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff Convolution

namespace UnforcedLeray.Leray

/-- Reflection of a scalar spatial test. -/
def reflectedTest (φ : Space → ℝ) : Space → ℝ := fun x => φ (-x)

theorem isSpatialTest_reflected {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    IsSpatialTest (reflectedTest φ) := by
  constructor
  · exact hφ.smooth.comp contDiff_neg
  · exact hφ.compact.comp_homeomorph (Homeomorph.neg Space)

theorem spatialTestDerivative_reflected (φ : Space → ℝ) (hφ : IsSpatialTest φ)
    (i : Fin 3) (x : Space) :
    spatialTestDerivative i (reflectedTest φ) x = -spatialTestDerivative i φ (-x) := by
  have hd := ((hφ.smooth.differentiable (by simp)) (-x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).neg)
  change (fderiv ℝ (φ ∘ (fun y : Space => -y)) x) (coordinateVector i) = _
  rw [hd.fderiv]
  simp [spatialTestDerivative]

/-- Actual scalar-test convolution with a vector-valued L² field. -/
def testConvolution (φ : Space → ℝ) (F : L2Space) : SpatialField :=
  φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (F : SpatialField)

/-- Every test-convolution value is a convergent Bochner integral. -/
theorem testConvolution_integrable (φ : Space → ℝ) (hφ : IsSpatialTest φ)
    (F : L2Space) (a : Space) :
    Integrable (fun x : Space => φ x • F (a - x)) volume :=
  hφ.compact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    hφ.continuous ((Lp.memLp F).locallyIntegrable (by norm_num)) a

/-- Compact smooth convolution is smooth even for an arbitrary L² input. -/
theorem testConvolution_smooth (φ : Space → ℝ) (hφ : IsSpatialTest φ) (F : L2Space) :
    ContDiff ℝ ∞ (testConvolution φ F) :=
  hφ.compact.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    hφ.smooth ((Lp.memLp F).locallyIntegrable (by norm_num))

/-- Differentiation falls on the genuine compact smooth convolution kernel. -/
theorem testConvolution_fderiv (φ : Space → ℝ) (hφ : IsSpatialTest φ)
    (F : L2Space) (i : Fin 3) (a : Space) :
    fderiv ℝ (testConvolution φ F) a (coordinateVector i) =
      testConvolution (spatialTestDerivative i φ) F a := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hd := hφ.compact.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip
    ((Lp.memLp F).locallyIntegrable (by norm_num)) hφ1 a
  rw [testConvolution, ← convolution_flip, hd.fderiv,
    convolution_precompR_apply _ ((Lp.memLp F).locallyIntegrable (by norm_num))
      (hφ.compact.fderiv ℝ) (hφ1.continuous_fderiv (by norm_num))]
  rw [testConvolution, ← convolution_flip]
  rfl

/-- The translated pairing is integrable for every shift. -/
theorem translation_testPairing_integrable (φ : Space → ℝ) (hφ : IsSpatialTest φ)
    (F : L2Space) (a : Space) :
    Integrable (fun x : Space => φ x • (translation a F) x) volume :=
  SobolevGraph.pairing_integrable φ hφ (translation a F)

/-- Lebesgue change of variables identifies a translated pairing with reflected convolution. -/
theorem translation_testPairing_eq_convolution (φ : Space → ℝ) (F : L2Space) (a : Space) :
    (∫ x : Space, φ x • (translation a F) x) =
      testConvolution (reflectedTest φ) F a := by
  calc
    (∫ x : Space, φ x • (translation a F) x) =
        ∫ x : Space, φ x • F (x + a) := by
      apply integral_congr_ae
      filter_upwards [coeFn_translation a F] with x hx
      rw [hx]
    _ = ∫ x : Space, φ (x - a) • F x := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (μ := (volume : Measure Space))
          (fun x : Space => φ (x - a) • F x) a)
    _ = testConvolution (reflectedTest φ) F a := by
      rw [testConvolution, convolution_eq_swap]
      change (∫ x : Space, φ (x - a) • F x) =
        ∫ x : Space, φ (-(a - x)) • F x
      simp only [neg_sub]

/-- The reflected kernel contributes the expected negative test derivative. -/
theorem reflected_testConvolution_fderiv (φ : Space → ℝ) (hφ : IsSpatialTest φ)
    (F : L2Space) (i : Fin 3) (a : Space) :
    fderiv ℝ (testConvolution (reflectedTest φ) F) a (coordinateVector i) =
      -(∫ x : Space, spatialTestDerivative i φ x • (translation a F) x) := by
  rw [testConvolution_fderiv _ (isSpatialTest_reflected hφ),
    translation_testPairing_eq_convolution]
  change (∫ x : Space, spatialTestDerivative i (reflectedTest φ) x • F (a - x)) =
    -(∫ x : Space, spatialTestDerivative i φ (-x) • F (a - x))
  simp_rw [spatialTestDerivative_reflected φ hφ, neg_smul]
  exact integral_neg _

/-- Every L² field has a differentiable compact-test pairing along translation orbits.
The derivative is computed on the test; no weak derivative of the field is assumed. -/
theorem hasDerivAt_translation_testPairing (φ : Space → ℝ) (hφ : IsSpatialTest φ)
    (F : L2Space) (i : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
      ∫ x : Space, φ x • (translation (s • coordinateVector i) F) x)
      (-(∫ x : Space, spatialTestDerivative i φ x •
        (translation (t • coordinateVector i) F) x)) t := by
  have hs := testConvolution_smooth (reflectedTest φ) (isSpatialTest_reflected hφ) F
  have hd := ((hs.differentiable (by simp))
    (t • coordinateVector i)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const (coordinateVector i))
  have he : (fun s : ℝ =>
      ∫ x : Space, φ x • (translation (s • coordinateVector i) F) x) =
      (fun s : ℝ => testConvolution (reflectedTest φ) F (s • coordinateVector i)) := by
    funext s
    exact translation_testPairing_eq_convolution φ F (s • coordinateVector i)
  rw [he]
  simpa only [Function.comp_def, id_eq, one_smul,
    reflected_testConvolution_fderiv φ hφ F i] using hd

/-- An actual L² weak derivative identifies the orbit derivative with the
pairing against the translated derivative field. -/
theorem hasDerivAt_translation_testPairing_of_weakDerivative (φ : Space → ℝ)
    (hφ : IsSpatialTest φ) (F G : L2Space) (i : Fin 3)
    (h : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
      ∫ x : Space, φ x • (translation (s • coordinateVector i) F) x)
      (∫ x : Space, φ x • (translation (t • coordinateVector i) G) x) t := by
  have ht : HasWeakSpatialDerivative i
      (translation (t • coordinateVector i) F : SpatialField)
      (translation (t • coordinateVector i) G : SpatialField) :=
    (weakDerivative_fieldTranslate (t • coordinateVector i) h).congr
      (coeFn_translation (t • coordinateVector i) F).symm
      (coeFn_translation (t • coordinateVector i) G).symm
  simpa only [ht.identity φ hφ, neg_neg] using
    hasDerivAt_translation_testPairing φ hφ F i t

/-- Each actual compact-test pairing orbit is continuous. -/
theorem continuous_translation_testPairing (φ : Space → ℝ) (hφ : IsSpatialTest φ)
    (F : L2Space) (i : Fin 3) :
    Continuous (fun t : ℝ =>
      ∫ x : Space, φ x • (translation (t • coordinateVector i) F) x) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_translation_testPairing φ hφ F i t).continuousAt

end UnforcedLeray.Leray
