import UnforcedLeray.Analysis.LerayProjection.TranslationL2
import UnforcedLeray.Analysis.LerayProjection.TranslationTests

/-!
# Translation invariance of the actual L² Leray projection

The test pullback calculation proves invariance of the concrete solenoidal
constraint. The unitary translation also preserves its orthogonal complement,
so uniqueness of the orthogonal decomposition proves projection commutation.
Neither invariance nor commutation is an assumed property.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace UnforcedLeray.Leray

/-- Translation preserves actual square integrability. -/
theorem fieldTranslate_memLp (a : Space) {f : SpatialField} (hf : MemLp f 2 volume) :
    MemLp (fieldTranslate a f) 2 volume :=
  hf.comp_measurePreserving (measurePreserving_add_right volume a)

/-- The bundled operator agrees with translation of square-integrable representatives. -/
theorem translation_toL2 (a : Space) {f : SpatialField} (hf : MemLp f 2 volume) :
    translation a (toL2 f) = toL2 (fieldTranslate a f) := by
  rw [toL2_of_memLp hf, toL2_of_memLp (fieldTranslate_memLp a hf)]
  rfl

/-- Actual weak solenoidality is preserved by the L² translation operator. -/
theorem translation_solenoidal (a : Space) {F : L2Space}
    (hF : IsSolenoidal (F : SpatialField)) :
    IsSolenoidal (translation a F : SpatialField) :=
  solenoidal_congr_ae (solenoidal_fieldTranslate a hF) (coeFn_translation a F).symm

theorem translation_solenoidal_iff (a : Space) (F : L2Space) :
    IsSolenoidal (translation a F : SpatialField) ↔ IsSolenoidal (F : SpatialField) := by
  constructor
  · intro h
    simpa only [translation_neg_cancel] using translation_solenoidal (-a) h
  · exact translation_solenoidal a

/-- The closed solenoidal subspace is invariant in both directions. -/
theorem translation_mem_solenoidal_iff (a : Space) (F : L2Space) :
    translation a F ∈ solenoidalSubspace ↔ F ∈ solenoidalSubspace := by
  rw [mem_solenoidalSubspace_iff, mem_solenoidalSubspace_iff]
  exact translation_solenoidal_iff a F

/-- The orthogonal complement is invariant because translations are invertible isometries. -/
theorem translation_mem_orthogonal (a : Space) {F : L2Space}
    (hF : F ∈ solenoidalSubspaceᗮ) : translation a F ∈ solenoidalSubspaceᗮ := by
  intro G hG
  calc
    inner ℝ G (translation a F) = inner ℝ (translation (-a) G) F := by
      simpa only [translation_cancel_neg] using
        (inner_translation a (translation (-a) G) F)
    _ = 0 := hF _ ((translation_mem_solenoidal_iff (-a) G).mpr hG)

/-- The L² Leray projection commutes with every actual spatial translation. -/
theorem projection_translation (a : Space) (F : L2Space) :
    projection (translation a F) = translation a (projection F) := by
  apply projection_eq_of_orthogonal
  · exact translation_solenoidal a (projection_solenoidal F)
  · rw [← map_sub]
    exact translation_mem_orthogonal a (residual_mem_orthogonal F)

/-- The same commutation identity as an equality of bounded linear operators. -/
theorem projection_comp_translation (a : Space) :
    projection.comp (translation a).toContinuousLinearMap =
      (translation a).toContinuousLinearMap.comp projection := by
  apply ContinuousLinearMap.ext
  intro F
  exact projection_translation a F

end UnforcedLeray.Leray
