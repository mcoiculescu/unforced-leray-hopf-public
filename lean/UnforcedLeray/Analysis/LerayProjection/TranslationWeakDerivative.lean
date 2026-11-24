import UnforcedLeray.Analysis.LerayProjection.TranslationTests
import UnforcedLeray.Analysis.WeakDerivative

/-!
# Translation of genuine weak spatial derivatives

The actual weak derivative relation is invariant under simultaneous spatial
translation of the field and its derivative. The proof uses inverse-shift
compact smooth tests and Lebesgue translation invariance for both vector-valued
pairings. In particular, both integrability guards are transported explicitly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Leray

/-- A weak spatial derivative translates together with its underlying field. -/
theorem weakDerivative_fieldTranslate (a : Space) {i : Fin 3} {f g : SpatialField}
    (h : HasWeakSpatialDerivative i f g) :
    HasWeakSpatialDerivative i (fieldTranslate a f) (fieldTranslate a g) := by
  constructor
  · intro φ hφ
    have hleft := (h.left_integrable (fun x => φ (x + -a))
      (isSpatialTest_translate (-a) hφ)).comp_add_right a
    simpa [fieldTranslate, spatialTestDerivative_translate] using hleft
  · intro φ hφ
    have hright := (h.right_integrable (fun x => φ (x + -a))
      (isSpatialTest_translate (-a) hφ)).comp_add_right a
    simpa [fieldTranslate] using hright
  · intro φ hφ
    have hleft :
        (∫ x : Space, spatialTestDerivative i φ x • fieldTranslate a f x) =
          ∫ x : Space, spatialTestDerivative i (fun y => φ (y + -a)) x • f x := by
      simpa [fieldTranslate, spatialTestDerivative_translate] using
        (integral_add_right_eq_self (μ := (volume : Measure Space))
          (fun x => spatialTestDerivative i (fun y => φ (y + -a)) x • f x) a)
    have hright :
        (∫ x : Space, φ x • fieldTranslate a g x) =
          ∫ x : Space, φ (x + -a) • g x := by
      simpa [fieldTranslate] using
        (integral_add_right_eq_self (μ := (volume : Measure Space))
          (fun x => φ (x + -a) • g x) a)
    rw [hleft, hright]
    exact h.identity _ (isSpatialTest_translate (-a) hφ)

/-- Simultaneous translation preserves and reflects the concrete weak derivative relation. -/
theorem hasWeakSpatialDerivative_fieldTranslate_iff (a : Space) (i : Fin 3)
    (f g : SpatialField) :
    HasWeakSpatialDerivative i (fieldTranslate a f) (fieldTranslate a g) ↔
      HasWeakSpatialDerivative i f g := by
  constructor
  · intro h
    simpa only [fieldTranslate_neg_cancel] using weakDerivative_fieldTranslate (-a) h
  · exact weakDerivative_fieldTranslate a

end UnforcedLeray.Leray
