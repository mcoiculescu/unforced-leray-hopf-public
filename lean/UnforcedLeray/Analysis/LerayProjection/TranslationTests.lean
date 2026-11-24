import UnforcedLeray.Analysis.LerayProjection.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Integral

/-!
# Spatial translation of genuine weak divergence tests

Translation acts on an actual field by `f(x + a)`. Compact smooth scalar tests
remain compact smooth after this pullback, and their coordinate derivatives
translate exactly. Lebesgue translation invariance then transports both the
integrability guards and the distributional divergence identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Leray

/-- Spatial translation of an actual vector field, using the convention `f(x + a)`. -/
def fieldTranslate (a : Space) (f : SpatialField) : SpatialField :=
  fun x => f (x + a)

@[simp] theorem fieldTranslate_zero (f : SpatialField) : fieldTranslate 0 f = f := by
  funext x
  simp [fieldTranslate]

@[simp] theorem fieldTranslate_neg_cancel (a : Space) (f : SpatialField) :
    fieldTranslate (-a) (fieldTranslate a f) = f := by
  funext x
  simp [fieldTranslate]

/-- Pullback by a translation preserves the actual compact smooth test class. -/
theorem isSpatialTest_translate (a : Space) {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    IsSpatialTest (fun x => φ (x + a)) := by
  constructor
  · exact hφ.smooth.comp (contDiff_id.add contDiff_const)
  · exact hφ.compact.comp_homeomorph (Homeomorph.addRight a)

/-- Coordinate differentiation commutes with spatial translation. -/
theorem spatialTestDerivative_translate (a : Space) (i : Fin 3) (φ : Space → ℝ)
    (x : Space) :
    spatialTestDerivative i (fun y => φ (y + a)) x =
      spatialTestDerivative i φ (x + a) := by
  simp only [spatialTestDerivative, fderiv_comp_add_right]

/-- Translation preserves weak divergence zero, including actual integrability. -/
theorem solenoidal_fieldTranslate (a : Space) {f : SpatialField} (hf : IsSolenoidal f) :
    IsSolenoidal (fieldTranslate a f) := by
  constructor
  · intro φ hφ
    have h := (hf.integrable (fun x => φ (x + -a))
      (isSpatialTest_translate (-a) hφ)).comp_add_right a
    simpa [fieldTranslate, spatialTestDerivative_translate] using h
  · intro φ hφ
    calc
      (∫ x : Space, ∑ i : Fin 3,
          (fieldTranslate a f x) i * spatialTestDerivative i φ x) =
          ∫ x : Space, ∑ i : Fin 3,
            (f x) i * spatialTestDerivative i (fun y => φ (y + -a)) x := by
        simpa [fieldTranslate, spatialTestDerivative_translate] using
          (integral_add_right_eq_self (μ := (volume : Measure Space))
            (fun x => ∑ i : Fin 3,
              (f x) i * spatialTestDerivative i (fun y => φ (y + -a)) x) a)
      _ = 0 := hf.identity _ (isSpatialTest_translate (-a) hφ)

/-- The translated field is solenoidal exactly when the original field is. -/
theorem isSolenoidal_fieldTranslate_iff (a : Space) (f : SpatialField) :
    IsSolenoidal (fieldTranslate a f) ↔ IsSolenoidal f := by
  constructor
  · intro h
    simpa only [fieldTranslate_neg_cancel] using solenoidal_fieldTranslate (-a) h
  · exact solenoidal_fieldTranslate a

end UnforcedLeray.Leray
