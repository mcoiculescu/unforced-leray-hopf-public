import UnforcedLeray.Short.PartIIb.Defs

/-!


Source of record: `the November 2 reference manuscript`, lines 1478-1480
(Fubini packaging) and 2370-2383 (use).

Take `W' := hW.meas.mk W`, a strongly measurable version of `W`. Translation in the first
variable preserves the product measure, so the a.e. periodicity transfers to `W'` and then to
almost every slice (`Measure.ae_ae_of_ae_prod`). The norm and the finiteness of the period
integral only see the a.e. class of the field.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace

theorem yqOfFields_slices (P : ℝ) [Fact (0 < P)] (W : ℝ × Space → CVec3) (hW : IsInYr P bgp W) :
    ∃ W' : ℝ × Space → CVec3, StronglyMeasurable W' ∧ W' =ᵐ[volume] W ∧
      (∀ᵐ τ : ℝ, (fun y => W' (τ + P, y)) =ᵐ[volume] fun y => W' (τ, y)) ∧
      phaseLpNorm P bgp W' = phaseLpNorm P bgp W ∧
      ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y, ‖W' (τ, y)‖ₑ ^ (ENNReal.ofReal bgp).toReal < ⊤ := by
  set W' := hW.meas.mk W with hW'def
  have hsm : StronglyMeasurable W' := hW.meas.stronglyMeasurable_mk
  have hE : W' =ᵐ[volume] W := hW.meas.ae_eq_mk.symm
  have hE' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)), W' x = W x := by
    rw [← Measure.volume_eq_prod]
    exact hE
  have hT : MeasurePreserving (fun x : ℝ × Space => (x.1 + P, x.2))
      ((volume : Measure ℝ).prod (volume : Measure Space))
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    (measurePreserving_add_right (volume : Measure ℝ) P).prod
      (MeasurePreserving.id (volume : Measure Space))
  have hShift : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)),
      W' (x.1 + P, x.2) = W' x := by
    have hper : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)),
        W (x.1 + P, x.2) = W x := by
      rw [← Measure.volume_eq_prod]
      exact hW.periodic
    filter_upwards [hT.quasiMeasurePreserving.ae hE', hper, hE'] with x h1 h2 h3
    exact h1.trans (h2.trans h3.symm)
  have hperiod : ∀ᵐ τ : ℝ, (fun y => W' (τ + P, y)) =ᵐ[volume] fun y => W' (τ, y) :=
    Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => W' (z.1 + P, z.2) = W' z) hShift
  have h2 : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, W' (τ, y) = W (τ, y) :=
    Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => W' z = W z) hE'
  have hnorm_eq : ∀ s : ℝ, ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W' (τ, y)‖ₑ ^ s
      = ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W (τ, y)‖ₑ ^ s := by
    intro s
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae h2] with τ hτ
    refine lintegral_congr_ae ?_
    filter_upwards [hτ] with y hy
    rw [hy]
  have hb : (ENNReal.ofReal bgp).toReal = bgp := ENNReal.toReal_ofReal (by norm_num [bgp])
  refine ⟨W', hsm, hE, hperiod, ?_, ?_⟩
  · unfold phaseLpNorm
    rw [hnorm_eq bgp]
  · rw [hb, hnorm_eq bgp]
    have hfin := hW.finite
    unfold phaseLpNorm at hfin
    have hI : ENNReal.ofReal P⁻¹ * ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W (τ, y)‖ₑ ^ bgp < ⊤ :=
      (ENNReal.rpow_lt_top_iff_of_pos (by norm_num [bgp])).1 hfin
    have hPne : ENNReal.ofReal P⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.2 (inv_pos.2 (inferInstance : Fact (0 < P)).out)).ne'
    exact ENNReal.lt_top_of_mul_ne_top_right hI.ne hPne

end UnforcedLeray.Short.IIb
