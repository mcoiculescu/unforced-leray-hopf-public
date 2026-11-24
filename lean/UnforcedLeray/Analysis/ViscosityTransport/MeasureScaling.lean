import UnforcedLeray.Analysis.ViscosityTransport.Defs
import UnforcedLeray.Analysis.SpatialScaling
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Spatial dilation on the actual spacetime slab measure

The time coordinate and interval are fixed. The pushforward of restricted
four-dimensional volume is computed by its product decomposition and the
three-dimensional spatial Haar Jacobian. Consequently integrability and Lp
membership are transported, rather than postulated.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace UnforcedLeray.ViscosityTransport

/-- Product decomposition of the actual measure used in the weak equation. -/
theorem slabMeasure_eq_prod (T : ℝ) :
    (volume : Measure SpaceTime).restrict (slab T) =
      ((volume : Measure ℝ).restrict (Ioo 0 T)).prod (volume : Measure Space) := by
  exact (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
    (ν := (volume : Measure Space)) (Ioo 0 T)).symm

/-- The spatial coordinate change is an actual measurable embedding of spacetime. -/
theorem spaceMap_measurableEmbedding {b : ℝ} (hb : b ≠ 0) :
    MeasurableEmbedding (spaceMap b) := by
  exact ((MeasurableEquiv.refl ℝ).prodCongr
    (Homeomorph.smulOfNeZero b hb).toMeasurableEquiv).measurableEmbedding

/-- Exact pushforward of volume restricted to the same time slab. -/
theorem map_spaceMap_slab (T : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Measure.map (spaceMap b) (volume.restrict (slab T)) =
      ENNReal.ofReal |(b ^ 3)⁻¹| • volume.restrict (slab T) := by
  rw [slabMeasure_eq_prod]
  change Measure.map (Prod.map id (fun x : Space => b • x))
      (((volume : Measure ℝ).restrict (Ioo 0 T)).prod (volume : Measure Space)) = _
  rw [← Measure.map_prod_map _ _ measurable_id (measurable_const_smul b),
    Measure.map_id, SpatialScaling.map_dilation hb, Measure.prod_smul_right]

/-- Dilation preserves genuine integrability on the unchanged time slab. -/
theorem integrableOn_comp_spaceMap {E : Type*} [NormedAddCommGroup E]
    {F : SpaceTime → E} {T b : ℝ}
    (hF : IntegrableOn F (slab T)) (hb : b ≠ 0) :
    IntegrableOn (F ∘ spaceMap b) (slab T) := by
  apply (spaceMap_measurableEmbedding hb).integrable_map_iff.mp
  rw [map_spaceMap_slab T hb]
  exact hF.smul_measure ENNReal.ofReal_ne_top

/-- Dilation preserves every Lp class on the spacetime slab. -/
theorem memLp_comp_spaceMap {E : Type*} [NormedAddCommGroup E]
    {F : SpaceTime → E} {p : ℝ≥0∞} {T b : ℝ}
    (hF : MemLp F p (volume.restrict (slab T))) (hb : b ≠ 0) :
    MemLp (F ∘ spaceMap b) p (volume.restrict (slab T)) := by
  apply (spaceMap_measurableEmbedding hb).memLp_map_measure_iff.mp
  rw [map_spaceMap_slab T hb]
  exact hF.smul_measure ENNReal.ofReal_ne_top

/-- Quasi-measure preservation, for jointly measurable representatives. -/
theorem spaceMap_quasiMeasurePreserving (T : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Measure.QuasiMeasurePreserving (spaceMap b) (volume.restrict (slab T))
      (volume.restrict (slab T)) := by
  refine ⟨(spaceMap_measurableEmbedding hb).measurable, ?_⟩
  rw [map_spaceMap_slab T hb]
  exact Measure.smul_absolutelyContinuous

/-- Joint almost-everywhere strong measurability survives spatial dilation. -/
theorem aestronglyMeasurable_comp_spaceMap {E : Type*} [NormedAddCommGroup E]
    {F : SpaceTime → E} {T b : ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (slab T))) (hb : b ≠ 0) :
    AEStronglyMeasurable (F ∘ spaceMap b) (volume.restrict (slab T)) :=
  hF.comp_quasiMeasurePreserving (spaceMap_quasiMeasurePreserving T hb)

/-- Iterated-integral Jacobian with the actual spatial dimension three.
Integrability hypotheses make the identity applicable to convergent weak pairings. -/
theorem iterated_integral_comp_spaceMap (F : SpaceTime → ℝ) (T b : ℝ)
    (_hF : IntegrableOn F (slab T)) (_hb : b ≠ 0) :
    (∫ t in Ioo (0 : ℝ) T, ∫ x : Space, F (spaceMap b (t, x))) =
      |(b ^ 3)⁻¹| * (∫ t in Ioo (0 : ℝ) T, ∫ x : Space, F (t, x)) := by
  have hi (t : ℝ) : (∫ x : Space, F (spaceMap b (t, x))) =
      |(b ^ 3)⁻¹| * (∫ x : Space, F (t, x)) := by
    simpa [spaceMap, Space, finrank_euclideanSpace, smul_eq_mul] using
      Measure.integral_comp_smul (volume : Measure Space) (fun x => F (t, x)) b
  simp_rw [hi]
  exact integral_const_mul _ _

end UnforcedLeray.ViscosityTransport
