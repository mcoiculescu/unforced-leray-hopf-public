import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs

/-!
# Time translation invariance of the lower Lebesgue integral on `ℝ × Space`

Source `the November 2 reference manuscript` 2667 (period shift `P = 2c/R`).
The map `(σ, z) ↦ (σ + t, z)` is measure preserving for the product measure, and it is a
measurable embedding, so no measurability hypothesis on the integrand is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem lintegral_shift_time (f : ℝ × Space → ℝ≥0∞) (t : ℝ) :
    ∫⁻ e : ℝ × Space, f (e.1 + t, e.2) = ∫⁻ e : ℝ × Space, f e := by
  have hmp : MeasurePreserving (fun e : ℝ × Space => (e.1 + t, e.2))
      (volume : Measure (ℝ × Space)) (volume : Measure (ℝ × Space)) := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right (volume : Measure ℝ) t).prod
      (MeasurePreserving.id (volume : Measure Space))
  have hemb : MeasurableEmbedding (fun e : ℝ × Space => (e.1 + t, e.2)) :=
    ((MeasurableEquiv.addRight t).prodCongr (MeasurableEquiv.refl Space)).measurableEmbedding
  exact hmp.lintegral_comp_emb hemb f

end UnforcedLeray.Short.PartIIIb.Concrete

end
