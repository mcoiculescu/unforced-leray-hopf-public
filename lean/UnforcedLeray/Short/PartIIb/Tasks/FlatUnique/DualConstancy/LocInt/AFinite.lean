import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Leaf `T11/2/1/3` (`A`-finiteness), proved from `InHr` by a measurable version of `b`,
slice a.e. equality, and the age-integral formula (`Axi.lintegral_ageμ`). -/
theorem DualFAFinite_proof : UnforcedLeray.Short.IIb.DualFAFinite := by
  intro c r b hc hr hb
  set e : ℝ := r / 2 - 5 / 2 with he
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hb' : AEStronglyMeasurable b (Axi.ageμ c e) := hb.meas
  set g : Coord → CMerid := hb'.mk b with hgdef
  have hg : Measurable g := hb'.stronglyMeasurable_mk.measurable
  have hbg : b =ᵐ[Axi.ageμ c e] g := hb'.ae_eq_mk
  -- finiteness of the age-weighted `r`-th power norm of `g`
  have h1 : ∫⁻ p, ‖b p‖ₑ ^ r ∂(Axi.ageμ c e) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := ENNReal.ofReal r) hp0 hpt).1
      hb.finite
    rwa [ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ r)] at h
  have hF : Measurable (fun p : Coord => ‖g p‖ₑ ^ r) := hg.enorm.pow_const r
  have h2 : ∫⁻ p, ‖g p‖ₑ ^ r ∂(Axi.ageμ c e) < ⊤ := by
    have heq : (fun p => ‖b p‖ₑ ^ r) =ᵐ[Axi.ageμ c e] (fun p => ‖g p‖ₑ ^ r) := by
      filter_upwards [hbg] with p hp
      rw [hp]
    rwa [lintegral_congr_ae heq] at h1
  -- the slice function `Φ σ = ∫ ‖g(σ,·)‖^r d avgμ`
  set Φ : ℝ → ℝ≥0∞ := fun σ => ∫⁻ x, ‖g (σ, x)‖ₑ ^ r ∂(Cyl.avgμ c) with hΦ
  -- the integral identity `∫ ‖g‖^r dageμ = ∫_{σ>0} σ^e Φ σ`
  have hB : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ e) * Φ s < ⊤ := by
    have e1 : ∫⁻ p, ‖g p‖ₑ ^ r ∂(Axi.ageμ c e)
        = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x in Cyl.cell c,
            ENNReal.ofReal (c⁻¹ * s ^ e) * ‖g (s, x)‖ₑ ^ r := by
      have hw : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ e) * ‖g p‖ₑ ^ r :=
        ((ENNReal.measurable_ofReal.comp
          (measurable_const.mul (measurable_fst.pow_const e)))).mul hF
      rw [Axi.lintegral_ageμ hc e hF, Measure.volume_eq_prod ℝ (ℝ × ℝ),
        ← Measure.prod_restrict, lintegral_prod _ hw.aemeasurable]
      rfl
    have e2 : ∀ s : ℝ, ∫⁻ x in Cyl.cell c, ENNReal.ofReal (c⁻¹ * s ^ e) * ‖g (s, x)‖ₑ ^ r
        = ENNReal.ofReal (s ^ e) * Φ s := by
      intro s
      have hΦs : Φ s = ENNReal.ofReal c⁻¹ * ∫⁻ x in Cyl.cell c, ‖g (s, x)‖ₑ ^ r := by
        simp only [hΦ, Cyl.avgμ, Cyl.cellμ]
        rw [lintegral_smul_measure, smul_eq_mul]
      rw [hΦs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
      ring
    have e3 : ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x in Cyl.cell c,
        ENNReal.ofReal (c⁻¹ * s ^ e) * ‖g (s, x)‖ₑ ^ r
        = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ e) * Φ s :=
      lintegral_congr fun s => e2 s
    rw [← e3, ← e1]
    exact h2
  -- `A^r` is the slice integral of `‖b‖^r`
  have hdf : ∀ σ : ℝ, dfA c r b σ ^ r = ∫⁻ x, ‖b (σ, x)‖ₑ ^ r ∂(Cyl.avgμ c) := by
    intro σ
    unfold dfA
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ r), one_div,
      ENNReal.rpow_inv_rpow (by linarith)]
  -- a.e. slice equality of `b` and `g`
  have hslice : ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ x ∂(Cyl.avgμ c), b (σ, x) = g (σ, x) := by
    have h3 : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
        fun s => ENNReal.ofReal (s ^ e)).prod (Cyl.avgμ c), b z = g z := by
      unfold Axi.ageμ at hbg
      exact hbg
    have : SFinite (Cyl.avgμ c) := by
      unfold Cyl.avgμ Cyl.cellμ
      infer_instance
    have h4 := Measure.ae_ae_of_ae_prod h3
    have hw : AEMeasurable (fun s : ℝ => ENNReal.ofReal (s ^ e))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const e)).aemeasurable
    have hne : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ENNReal.ofReal (s ^ e) ≠ 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs e)).ne'
    exact (withDensity_absolutelyContinuous' hw hne).ae_le h4
  -- conclusion
  have hae : ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))),
      ENNReal.ofReal (σ ^ e) * dfA c r b σ ^ r = ENNReal.ofReal (σ ^ e) * Φ σ := by
    filter_upwards [hslice] with σ hσ
    rw [hdf σ, hΦ]
    congr 1
    dsimp only
    exact lintegral_congr_ae (hσ.mono fun x hx => by simp only [hx])
  rw [lintegral_congr_ae hae]
  exact hB

end UnforcedLeray.Short.IIb
