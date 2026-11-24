import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas

/-!
# `VtvEnergyBand`: energy fields are `L²` on age bands (source 3426-3430)

Pointwise `‖b_i‖² ≤ vnorm2(b)² + tnorm2(G)²`, and the energy integral over `Icc s₁ s₂' ×ˢ cell`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvEnergyBand : VtvEnergyBand := by
  intro c b G hE s₁ s₂ hs₁ i
  obtain ⟨s₂', hs₂'⟩ : ∃ t : ℝ, t = max s₂ (s₁ + 1) := ⟨_, rfl⟩
  have hlt : s₁ < s₂' := by
    rw [hs₂']
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hen := hE.energyLoc s₁ s₂' hs₁ hlt
  have hsub : Icc s₁ s₂ ×ˢ B0579.cell c ⊆ Icc s₁ s₂' ×ˢ B0579.cell c := by
    refine prod_mono (Icc_subset_Icc_right ?_) Subset.rfl
    rw [hs₂']
    exact le_max_left _ _
  have hasm : AEStronglyMeasurable (fun p => b p i)
      (volume.restrict (Icc s₁ s₂' ×ˢ B0579.cell c)) :=
    (hE.measurable i).aestronglyMeasurable
  have hbig : MemLp (fun p => b p i) 2 (volume.restrict (Icc s₁ s₂' ×ˢ B0579.cell c)) := by
    refine (memLp_two_iff_integrable_sq_norm hasm).2 ⟨?_, ?_⟩
    · exact ((hE.measurable i).norm.pow_const 2).aestronglyMeasurable
    · unfold HasFiniteIntegral
      refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hen
      rw [Real.enorm_eq_ofReal (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have h1 := UnforcedLeray.Short.IIIa.fib_norm_le_vnorm2 (b p) i
      have hv0 : 0 ≤ UnforcedLeray.Short.IIIa.vnorm2 (b p) := Real.sqrt_nonneg _
      have ht0 : 0 ≤ UnforcedLeray.Short.IIIa.tnorm2 (G p) := Real.sqrt_nonneg _
      nlinarith [mul_nonneg (sub_nonneg.2 h1) hv0, mul_nonneg (sub_nonneg.2 h1) (norm_nonneg (b p i)),
        sq_nonneg (UnforcedLeray.Short.IIIa.tnorm2 (G p))]
  exact MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hbig

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
