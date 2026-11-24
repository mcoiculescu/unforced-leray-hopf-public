import UnforcedLeray.Short.PartIIb.Sub.T12_2

/-!
# Part II-b, leaf `PartII-b:T12/2/2` (`SliceCylLpAe`): a.e. slice of an `H_r` profile is `CylLp`

Source of record: `the November 2 reference manuscript`, lines 1923-1926.
Target: `UnforcedLeray.Short.IIb.LerayLiftSub.SliceCylLpAe` (`Sub/T12_2.lean`).

Proof: `hNorm c r F' < ⊤` unfolds to a finite `∫⁻ ‖F'‖ₑ^r d(ageμ c a)`. Since `ageμ` is the product of
the weighted measure `s^a ds` on `(0,∞)` with the normalized cell measure, Tonelli (`lintegral_prod`)
and `lintegral_withDensity_eq_lintegral_mul` give `∫⁻ s^a ∫⁻ z ‖F'(s,z)‖ₑ^r dz ds < ⊤`. Since the
weight is positive and finite for `s > 0`, the inner slice integral is finite for a.e. `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem sliceCylLpAe_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SliceCylLpAe := by
  intro c r hc hr F' hF' hper hfin
  have hr0 : 0 < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr0).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeas : Measurable F' := hF'.measurable
  have hgm : Measurable fun p : ℝ × (ℝ × ℝ) => ‖F' p‖ₑ ^ r := hmeas.enorm.pow_const r
  -- finiteness of the full age integral
  have hI : ∫⁻ p, ‖F' p‖ₑ ^ r ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) < ⊤ := by
    have h := hfin
    unfold UnforcedLeray.Short.IIb.hNorm UnforcedLeray.Short.IIb.hMeas at h
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt, ENNReal.toReal_ofReal hr0.le] at h
    exact h
  haveI hSF : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    infer_instance
  set w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) with hw_def
  have hw_meas : Measurable w := UnforcedLeray.Axi.measurable_ofReal_rpow _
  have hI' : ∫⁻ p, ‖F' p‖ₑ ^ r ∂(((volume.restrict (Ioi (0 : ℝ))).withDensity w).prod
      (UnforcedLeray.Cyl.avgμ c)) < ⊤ := hI
  rw [lintegral_prod _ hgm.aemeasurable] at hI'
  set G : ℝ → ℝ≥0∞ := fun s => ∫⁻ z, ‖F' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) with hG_def
  have hGm : Measurable G := hgm.lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hw_meas hGm] at hI'
  have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), (w * G) s < ⊤ :=
    ae_lt_top (hw_meas.mul hGm) hI'.ne
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with s hs hs0
  have hs0' : (0 : ℝ) < s := hs0
  have hwpos : w s ≠ 0 := by
    simp only [hw_def]
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hs0' _)).ne'
  have hGfin : G s < ⊤ := by
    have hs' : w s * G s < ⊤ := hs
    rcases ENNReal.mul_lt_top_iff.1 hs' with h | h | h
    · exact h.2
    · exact absurd h hwpos
    · rw [h]; exact ENNReal.zero_lt_top
  have hmem : MemLp (fun z => F' (s, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
    refine ⟨(hF'.comp_measurable measurable_prodMk_left).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt, ENNReal.toReal_ofReal hr0.le]
    exact hGfin
  exact ⟨fun z => hper s z, hmem⟩

end UnforcedLeray.Short.IIb
