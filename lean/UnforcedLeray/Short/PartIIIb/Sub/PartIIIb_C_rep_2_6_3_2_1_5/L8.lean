import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5

/-!
# `gkerMajShiftIntegrable` (`PartIII-b:C/rep/2/6/3/2/1/5/8`)

Source `shorter-proof-2026-11-02.tex` 3603-3626, 3800-3807, 4171-4200.
The reflection `(s,z) ↦ (t₀ - s, z)` preserves `volume.prod volume`. The integrand is
`(B.indicator G) ∘ R` with `B = Ioi 0 ×ˢ univ`: `t₀ - s > 0` exactly when `s < t₀`. The indicator
of `B` is integrable since `(volume.prod volume).restrict B = (volume.restrict (Ioi 0)).prod volume`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gkerMajShiftIntegrable : GkerMajShiftIntegrable := by
  intro G t₀ hG
  have hB : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set Space)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have e : (volume.prod volume : Measure (ℝ × Space)).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set Space)) =
      (volume.restrict (Ioi (0 : ℝ))).prod volume := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hGB : Integrable ((Ioi (0 : ℝ) ×ˢ (univ : Set Space)).indicator G) (volume.prod volume) := by
    rw [integrable_indicator_iff hB, IntegrableOn, e]
    exact hG
  have hR : MeasurePreserving (Prod.map (fun s : ℝ => t₀ - s) id)
      (volume.prod volume) (volume.prod volume) :=
    (Measure.measurePreserving_sub_left (volume : Measure ℝ) t₀).prod
      (MeasurePreserving.id (volume : Measure Space))
  have hfeq : (fun p : ℝ × Space => if p.1 < t₀ then G (t₀ - p.1, p.2) else 0) =
      (Ioi (0 : ℝ) ×ˢ (univ : Set Space)).indicator G ∘ Prod.map (fun s : ℝ => t₀ - s) id := by
    funext p
    by_cases h : p.1 < t₀
    · have h1 : t₀ - p.1 ∈ Ioi (0 : ℝ) := sub_pos.2 h
      simp [Prod.map, h, h1]
    · have h1 : t₀ - p.1 ∉ Ioi (0 : ℝ) := fun h' => h (sub_pos.1 h')
      simp [Prod.map, h, h1]
  rw [hfeq]
  exact (hR.integrable_comp hGB.aestronglyMeasurable).mpr hGB

end UnforcedLeray.Short.PartIIIb.Concrete
