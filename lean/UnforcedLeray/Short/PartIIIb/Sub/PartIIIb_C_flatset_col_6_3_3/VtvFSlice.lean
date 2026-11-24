import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.BandVanish

/-!
# Almost every slice of `f` is `L¹` on every box (source 3511-3514, 4464-4467)

The sixth clause of `VtvHyps` says `f_i ∈ L²([s₁,s₂] × cell)`.  By Fubini, for almost every age
`s ∈ [s₁,s₂]` the slice `x ↦ f(s,x) i` is `L²` on the cell (its square is integrable, and it is
almost everywhere strongly measurable through a measurable modification of `f`), hence `L¹` on
every finite-measure box `cell ∩ {|η| ≤ R}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvFSlice : VtvFSlice := by
  intro ν c μ tr ω g b G f H s₁ s₂ hs₁
  have hf := H.2.2.2.2.2.1 s₁ s₂ hs₁
  have hae : ∀ i : Fin 2, ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)),
      Integrable (fun y => ‖f (s, y) i‖ ^ 2) (volume.restrict (B0579.cell c)) ∧
      AEStronglyMeasurable (fun y => f (s, y) i) (volume.restrict (B0579.cell c)) := by
    intro i
    have hT : (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c))
        = (volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c)) :=
      (Measure.prod_restrict _ _).symm
    have hM : MemLp (fun p : ℝ × (ℝ × ℝ) => f p i) 2
        ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))) := by
      rw [← hT]
      exact hf i
    have hI : Integrable (fun p : ℝ × (ℝ × ℝ) => ‖f p i‖ ^ 2)
        ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))) :=
      hM.norm.integrable_sq
    have hae1 : ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)),
        Integrable (fun y => ‖f (s, y) i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
      hI.prod_right_ae
    have hgm : ∀ᵐ z ∂((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))),
        f z i = hM.1.mk (fun p : ℝ × (ℝ × ℝ) => f p i) z :=
      hM.1.ae_eq_mk
    have hae3 := Measure.ae_ae_of_ae_prod hgm
    have hgs : StronglyMeasurable (hM.1.mk (fun p : ℝ × (ℝ × ℝ) => f p i)) :=
      hM.1.stronglyMeasurable_mk
    have hae2 : ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)),
        AEStronglyMeasurable (fun y => f (s, y) i) (volume.restrict (B0579.cell c)) := by
      filter_upwards [hae3] with s hs
      exact ((hgs.comp_measurable (measurable_prodMk_left (x := s))).aestronglyMeasurable).congr
        (hs.mono fun y hy => hy.symm)
    filter_upwards [hae1, hae2] with s h1 h2
    exact ⟨h1, h2⟩
  have hall : ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)), ∀ i : Fin 2,
      Integrable (fun y => ‖f (s, y) i‖ ^ 2) (volume.restrict (B0579.cell c)) ∧
      AEStronglyMeasurable (fun y => f (s, y) i) (volume.restrict (B0579.cell c)) :=
    ae_all_iff.2 hae
  filter_upwards [hall] with s hs
  intro R i
  obtain ⟨h1, h2⟩ := hs i
  have hsq : Integrable (fun y => ‖f (s, y) i‖ ^ 2) (volume.restrict (vtvBox c R)) :=
    h1.mono_measure (Measure.restrict_mono (vtvBox_subset_cell c R) le_rfl)
  have hone : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) (volume.restrict (vtvBox c R)) := by
    have : IsFiniteMeasure (volume.restrict (vtvBox c R)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact volume_vtvBox_lt_top c R⟩
    exact integrable_const 1
  show Integrable (fun y => f (s, y) i) (volume.restrict (vtvBox c R))
  refine Integrable.mono' (hone.add hsq)
    (h2.mono_measure (Measure.restrict_mono (vtvBox_subset_cell c R) le_rfl))
    (Eventually.of_forall fun y => ?_)
  show ‖f (s, y) i‖ ≤ 1 + ‖f (s, y) i‖ ^ 2
  nlinarith [sq_nonneg (‖f (s, y) i‖ - 1 / 2)]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
