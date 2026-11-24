import UnforcedLeray.Analysis.LerayProjection.TranslationPairing
import UnforcedLeray.Analysis.LerayProjection.Translation
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weak derivatives are the actual strong generators of L² translations

Compact smooth tests separate L² classes. The exact derivative of each test
pairing and the fundamental theorem of calculus give an L²-valued integral
identity for fields with an actual weak derivative. Consequently their
translation orbits are strongly differentiable. The converse follows by
differentiating test pairings. This identifies the concrete weak derivative
graph with the infinitesimal generator, without a density assumption.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Leray

open SobolevGraph

/-- Compact smooth scalar tests against constant vectors separate actual L² classes. -/
theorem eq_of_testPairings {F G : L2Space}
    (h : ∀ φ : Space → ℝ, ∀ hφ : IsSpatialTest φ, ∀ v : Space,
      pairing φ hφ v F = pairing φ hφ v G) : F = G := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp F).locallyIntegrable (by norm_num))
    ((Lp.memLp G).locallyIntegrable (by norm_num))
  intro φ hs hc
  apply ext_inner_left ℝ
  intro v
  exact (pairing_apply φ ⟨hs,hc⟩ v F).symm.trans
    ((h φ ⟨hs,hc⟩ v).trans (pairing_apply φ ⟨hs,hc⟩ v G))

/-- Scalarized derivative identity for the actual translated weak field. -/
theorem hasDerivAt_pairing_translation_of_weakDerivative
    (φ : Space → ℝ) (hφ : IsSpatialTest φ) (v : Space)
    (F G : L2Space) (i : Fin 3)
    (h : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => pairing φ hφ v (translation (s • coordinateVector i) F))
      (pairing φ hφ v (translation (t • coordinateVector i) G)) t := by
  simpa only [Function.comp_def, innerSL_apply_apply, pairing_apply] using
    (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_translation_testPairing_of_weakDerivative φ hφ F G i h t)

/-- A weak derivative gives the genuine Bochner integral increment of its L² field. -/
theorem translation_eq_add_integral_weakDerivative (F G : L2Space) (i : Fin 3)
    (h : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) (t : ℝ) :
    translation (t • coordinateVector i) F =
      F + ∫ s in (0 : ℝ)..t, translation (s • coordinateVector i) G := by
  have hc : Continuous (fun s : ℝ => translation (s • coordinateVector i) G) :=
    (continuous_translation_orbit G).comp (continuous_id.smul continuous_const)
  apply eq_of_testPairings
  intro φ hφ v
  rw [map_add, ← (pairing φ hφ v).intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_hs : s ∈ uIcc (0 : ℝ) t) =>
      hasDerivAt_pairing_translation_of_weakDerivative φ hφ v F G i h s)
    (((pairing φ hφ v).continuous.comp hc).intervalIntegrable 0 t)
  simp only [zero_smul, translation_zero] at hFTC
  rw [hFTC]
  ring

/-- Actual L² weak differentiation is strong differentiation of the translation orbit. -/
theorem hasDerivAt_translation_of_weakDerivative (F G : L2Space) (i : Fin 3)
    (h : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => translation (s • coordinateVector i) F)
      (translation (t • coordinateVector i) G) t := by
  have hc : Continuous (fun s : ℝ => translation (s • coordinateVector i) G) :=
    (continuous_translation_orbit G).comp (continuous_id.smul continuous_const)
  have he : (fun s : ℝ => translation (s • coordinateVector i) F) =
      (fun s : ℝ => F + ∫ r in (0 : ℝ)..s, translation (r • coordinateVector i) G) := by
    funext s
    exact translation_eq_add_integral_weakDerivative F G i h s
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add F

/-- Conversely, a strong translation derivative is the concrete distributional derivative. -/
theorem weakDerivative_of_hasDerivAt_translation (F G : L2Space) (i : Fin 3)
    (h : HasDerivAt (fun s : ℝ => translation (s • coordinateVector i) F) G 0) :
    HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField) := by
  refine ⟨fun φ hφ => pairing_integrable _ (hφ.derivative i) F,
    fun φ hφ => pairing_integrable φ hφ G, ?_⟩
  intro φ hφ
  apply ext_inner_left ℝ
  intro v
  have h₁ := (pairing φ hφ v).hasFDerivAt.comp_hasDerivAt 0 h
  have h₂ := (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_translation_testPairing φ hφ F i 0)
  simp only [Function.comp_def, pairing_apply] at h₁
  simp only [Function.comp_def, innerSL_apply_apply] at h₂
  have he := h₁.unique h₂
  simp only [zero_smul, translation_zero, inner_neg_right] at he ⊢
  linarith

/-- Exact generator characterization, with neither direction as an assumption. -/
theorem weakDerivative_iff_hasDerivAt_translation (F G : L2Space) (i : Fin 3) :
    HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField) ↔
      HasDerivAt (fun s : ℝ => translation (s • coordinateVector i) F) G 0 := by
  constructor
  · intro h
    simpa only [zero_smul, translation_zero] using
      hasDerivAt_translation_of_weakDerivative F G i h 0
  · exact weakDerivative_of_hasDerivAt_translation F G i

/-- The actual L² Leray projection commutes with actual weak spatial differentiation. -/
theorem weakDerivative_projection (F G : L2Space) (i : Fin 3)
    (h : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) :
    HasWeakSpatialDerivative i (projection F : SpatialField) (projection G : SpatialField) := by
  apply weakDerivative_of_hasDerivAt_translation
  have hd := projection.hasFDerivAt.comp_hasDerivAt 0
    ((weakDerivative_iff_hasDerivAt_translation F G i).mp h)
  simpa only [Function.comp_def, projection_translation] using hd

end UnforcedLeray.Leray
