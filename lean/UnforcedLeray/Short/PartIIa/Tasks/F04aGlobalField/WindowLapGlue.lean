import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1

/-!
# Part II-a, task `PartII-a:F04/1/5`: gluing of the window Laplacians

Proves the Prop `WindowLapGlue` (Sub E of `Sub/PartIIa_F04_1.lean`).
Representatives `g k` of the `Λk k` are glued by the piecewise rule `Λ p = g ⌊p.1⌋ p`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.PhaseSpace
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Passing an a.e. statement on `S ∩ T` to an a.e. statement on `S`, conditional on `x ∈ T`. -/
theorem ae_restrict_imp_of_inter {α : Type*} [MeasurableSpace α] {μ : Measure α} {S T : Set α}
    (hS : MeasurableSet S) (hT : MeasurableSet T) {P : α → Prop}
    (h : ∀ᵐ x ∂μ.restrict (S ∩ T), P x) : ∀ᵐ x ∂μ.restrict S, x ∈ T → P x := by
  rw [ae_restrict_iff' hS]
  rw [ae_restrict_iff' (hS.inter hT)] at h
  filter_upwards [h] with x hx hxS hxT
  exact hx ⟨hxS, hxT⟩

theorem measurableSet_winSet' (τ : ℝ) : MeasurableSet (winSet τ) :=
  measurableSet_Ioo.prod MeasurableSet.univ

theorem mem_winSet_floor (p : ℝ × Space) : p ∈ winSet (((⌊p.1⌋ : ℤ)) : ℝ) :=
  ⟨⟨by linarith [Int.floor_le p.1], by linarith [Int.lt_floor_add_one p.1]⟩, mem_univ _⟩

theorem windowLapGlue : WindowLapGlue := by
  unfold WindowLapGlue
  intro Λk hmeas hover
  obtain ⟨g, hgs, hgae⟩ : ∃ g : ℤ → ℝ × Space → CVec3,
      (∀ k : ℤ, StronglyMeasurable (g k)) ∧
        ∀ k : ℤ, Λk k =ᵐ[volume.restrict (winSet (k : ℝ))] g k :=
    ⟨fun k => (hmeas k).mk (Λk k), fun k => (hmeas k).stronglyMeasurable_mk,
      fun k => (hmeas k).ae_eq_mk⟩
  have hgg : ∀ k l : ℤ, ∀ᵐ p ∂(volume.restrict (winSet (k : ℝ) ∩ winSet (l : ℝ))),
      g k p = g l p := by
    intro k l
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hgae k),
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hgae l),
      hover k l] with p h1 h2 h3
    exact h1.symm.trans (h3.trans h2)
  have key : ∀ k : ℤ, ∀ᵐ p ∂(volume.restrict (winSet (k : ℝ))),
      ∀ l : ℤ, p ∈ winSet (l : ℝ) → g k p = g l p := by
    intro k
    rw [ae_all_iff]
    intro l
    exact ae_restrict_imp_of_inter (measurableSet_winSet' _) (measurableSet_winSet' _) (hgg k l)
  have hFm : Measurable (fun q : (ℝ × Space) × ℤ => g q.2 q.1) :=
    measurable_from_prod_countable_left (fun k => (hgs k).measurable)
  have hPm : Measurable (fun p : ℝ × Space => (p, ⌊p.1⌋)) :=
    measurable_id.prodMk (Int.measurable_floor.comp measurable_fst)
  have hΛm : Measurable (fun p : ℝ × Space => g ⌊p.1⌋ p) := hFm.comp hPm
  refine ⟨fun p => g ⌊p.1⌋ p, hΛm.stronglyMeasurable, fun k => ?_⟩
  filter_upwards [key k, hgae k] with p hp1 hp2
  show g ⌊p.1⌋ p = Λk k p
  rw [hp2]
  exact (hp1 _ (mem_winSet_floor p)).symm

end UnforcedLeray.Short.PartIIa
