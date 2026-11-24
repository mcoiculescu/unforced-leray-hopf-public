import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_2.Global
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_2.Contract
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1

/-!
# Spatial mollification preserves local `L^p`

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`), 2525-2531.

Localisation as in `spatMol_tendsto_lp_of`: on the cell `(0,P] × B(0,R)` the mollification of `f`
only sees `f` on `(0,P] × B(0,R + r)` where `tsupport ρ ⊆ B(0,r)`.  Contraction
(`spatMolContract_holds`) and measurability (`spatMolGl_aesm`) of the mollified indicator give
`L^p` on the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Mollification preserves local `L^p`** (source 2562-2564). -/
theorem spatMol_memLoc : SpatMolMemLoc := by
  intro P _ ρ hρs hρc hρ0 hρ1 f p hp1 hpt hf
  obtain ⟨r, hr⟩ := hρc.isCompact.isBounded.subset_closedBall (0 : UnforcedLeray.Space)
  have hρcont : Continuous ρ := hρs.continuous
  intro R
  set A : Set (ℝ × UnforcedLeray.Space) := Ioc (0 : ℝ) P ×ˢ Metric.closedBall 0 R with hAdef
  set A' : Set (ℝ × UnforcedLeray.Space) := Ioc (0 : ℝ) P ×ˢ Metric.closedBall 0 (R + r)
    with hA'def
  have hA : MeasurableSet A := measurableSet_Ioc.prod Metric.isClosed_closedBall.measurableSet
  have hA' : MeasurableSet A' := measurableSet_Ioc.prod Metric.isClosed_closedBall.measurableSet
  have hμ : (volume.restrict (Ioc (0 : ℝ) P)).prod (volume.restrict (Metric.closedBall 0 R))
      = (volume : Measure (ℝ × UnforcedLeray.Space)).restrict A := by
    rw [hAdef, Measure.volume_eq_prod, Measure.prod_restrict]
  have hμ' : (volume.restrict (Ioc (0 : ℝ) P)).prod (volume.restrict (Metric.closedBall 0 (R + r)))
      = (volume : Measure (ℝ × UnforcedLeray.Space)).restrict A' := by
    rw [hA'def, Measure.volume_eq_prod, Measure.prod_restrict]
  have hft : MemLp (A'.indicator f) p volume := by
    rw [memLp_indicator_iff_restrict hA']
    rw [← hμ']
    exact hf (R + r)
  have hG : MemLp (spatMol ρ (A'.indicator f)) p volume := by
    refine ⟨spatMolGl_aesm ρ hρcont (A'.indicator f) hft.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt
      (spatMolContract_holds p hp1 hpt ρ hρs hρc hρ0 hρ1 _ hft) hft.eLpNorm_lt_top
  have hfg : spatMol ρ f =ᵐ[volume.restrict A] spatMol ρ (A'.indicator f) := by
    refine (ae_restrict_iff' hA).2 (Filter.Eventually.of_forall ?_)
    rintro ⟨τ, y⟩ hx
    have hτ : τ ∈ Ioc (0 : ℝ) P := hx.1
    have hy : ‖y‖ ≤ R := by simpa using hx.2
    unfold spatMol
    refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
    show (ρ y' : ℂ) * f (τ, y - y') = (ρ y' : ℂ) * A'.indicator f (τ, y - y')
    by_cases h0 : ρ y' = 0
    · simp [h0]
    · have hy' : y' ∈ tsupport ρ := subset_tsupport _ (Function.mem_support.2 h0)
      have h1 : ‖y'‖ ≤ r := by simpa using hr hy'
      have h2 : ‖y - y'‖ ≤ R + r := (norm_sub_le _ _).trans (add_le_add hy h1)
      rw [Set.indicator_of_mem (show (τ, y - y') ∈ A' from ⟨hτ, by simpa using h2⟩)]
  rw [hμ]
  exact MemLp.ae_eq hfg.symm (hG.restrict A)

end UnforcedLeray.Short.PartIIIb.Concrete
