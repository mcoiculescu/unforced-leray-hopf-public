import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props

/-!
# `FUWindowR` (item `PartIII-b:C/near/delta/9/1/1`)

Source `the November 2 reference manuscript`
3541-3545: on the window `(0,T)` the difference solves the homogeneous equation, so the source
pairing `R(s) = ∫_cell Re⟨F(s), G(s)⟩` vanishes for a.e. `s ∈ (0,T)` (Fubini).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem fuWindowR : FUWindowR := by
  intro c F G T h
  have hprod : (volume : Measure (ℝ × (ℝ × ℝ))).restrict
      (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [hprod] at h
  have h2 := Measure.ae_ae_of_ae_prod h
  have h3 : ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) T)), ∀ᵐ x ∂(volume.restrict
      (UnforcedLeray.B0579.cell c)), s < T → ∀ i j, F (s, x) i j = 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self h2
  filter_upwards [h3, ae_restrict_mem measurableSet_Ioo] with s hs hsT
  unfold UnforcedLeray.Short.IIIa.energyR
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hs] with x hx
  have hF := hx hsT.2
  simp [hF]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
