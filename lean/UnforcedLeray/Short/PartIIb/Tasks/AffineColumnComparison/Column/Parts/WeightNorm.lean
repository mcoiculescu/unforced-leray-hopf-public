import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.WeightNorm.EtaInt

/-!
# `PartII-b:G4/3/7/1` : `ColWeightNorm`

Source: `the November 2 reference manuscript` lines 2370-2374, 2385
(the integrability exponent `-9/8 + p = 13/8 > -1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open WeightNormAux

/-- **`ColWeightNorm`** (SP 2385). -/
theorem colWeightNorm : UnforcedLeray.Short.IIb.ColWeightNorm := by
  intro N κ hκ
  set q : ℝ := 11 / 4 with hq
  have hq0 : 0 < q := by rw [hq]; norm_num
  obtain ⟨K', hK', hE⟩ := lintegral_eta_le (m := (N : ℝ) * q) (b := q * κ) (by positivity)
    (by positivity)
  refine ⟨K' ^ (1 / q), by positivity, ?_⟩
  intro c H M f hc hH hM hvan hbd
  have hc0 : 0 < c := by linarith
  set a : ℝ := bgp / 2 - 5 / 2 with ha
  have haq : a + q = 13 / 8 := by rw [ha, hq]; unfold bgp; norm_num
  have hbgp : ENNReal.ofReal bgp = ENNReal.ofReal q := by unfold bgp; rw [hq]
  have htr : (ENNReal.ofReal bgp).toReal = q := by
    rw [hbgp, ENNReal.toReal_ofReal hq0.le]
  -- the majorant
  set φ : ℝ → ℝ≥0∞ := Set.indicator (Ioc 0 (H / 2)) (fun s => ENNReal.ofReal (M * s)) with hφ
  set ψ : ℝ → ℝ≥0∞ := fun η => ENNReal.ofReal
    ((1 + |η|) ^ N * Real.exp (-(κ * |η| / c))) with hψ
  have hφm : Measurable φ := by
    rw [hφ]
    exact (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)).indicator
      measurableSet_Ioc
  have hψm : Measurable ψ := by
    rw [hψ]
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hmaj : ∀ᵐ x ∂(hMeas c bgp), ‖f x‖ₑ ≤ φ x.1 * ψ x.2.2 := by
    have hae := Axi.ae_ageμ_mem hc0 a
    filter_upwards [hae] with x hx
    have hs : 0 < x.1 := hx.1
    by_cases hle : x.1 ≤ H / 2
    · have hmem : x.1 ∈ Ioc 0 (H / 2) := ⟨hs, hle⟩
      rw [hφ, indicator_of_mem hmem, hψ, ← ENNReal.ofReal_mul (by positivity),
        ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      have := hbd x hs hle
      calc ‖f x‖ ≤ _ := this
        _ = _ := by ring
    · have : f x = 0 := hvan x (not_le.1 hle)
      rw [this]; simp
  -- lintegral bound
  have hmeasG : Measurable fun x : Coord => (φ x.1 * ψ x.2.2) ^ q := by
    have : Measurable fun x : Coord => φ x.1 * ψ x.2.2 :=
      (hφm.comp measurable_fst).mul (hψm.comp (measurable_snd.comp measurable_snd))
    exact this.pow_const q
  have hint : ∫⁻ x, ‖f x‖ₑ ^ q ∂(hMeas c bgp) ≤
      ENNReal.ofReal (M ^ q * (H / 2) ^ ((21 : ℝ) / 8) * K' * c ^ ((N : ℝ) * q + 1)) := by
    calc ∫⁻ x, ‖f x‖ₑ ^ q ∂(hMeas c bgp)
        ≤ ∫⁻ x, (φ x.1 * ψ x.2.2) ^ q ∂(hMeas c bgp) :=
          lintegral_mono_ae (hmaj.mono fun x hx => ENNReal.rpow_le_rpow hx hq0.le)
      _ = ∫⁻ x in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
            ENNReal.ofReal (c⁻¹ * x.1 ^ a) * (φ x.1 * ψ x.2.2) ^ q := by
          unfold hMeas
          exact Axi.lintegral_ageμ hc0 a hmeasG
      _ = ∫⁻ x in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
            (ENNReal.ofReal (c⁻¹ * x.1 ^ a) * φ x.1 ^ q) * ψ x.2.2 ^ q := by
          refine lintegral_congr fun x => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]; ring
      _ = (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (c⁻¹ * s ^ a) * φ s ^ q) *
            (ENNReal.ofReal c * ∫⁻ η : ℝ, ψ η ^ q) := by
          have hv : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell c) =
              (volume.restrict (Ioi (0 : ℝ))).prod
                ((volume.restrict (Ico (-c / 2) (c / 2))).prod (volume.restrict (univ : Set ℝ))) := by
            unfold Axi.qCell
            rw [Measure.volume_eq_prod, Measure.volume_eq_prod, Measure.prod_restrict,
              Measure.prod_restrict]
          rw [Measure.restrict_univ] at hv
          rw [hv]
          have hA : Measurable fun s : ℝ => ENNReal.ofReal (c⁻¹ * s ^ a) * φ s ^ q :=
            (ENNReal.measurable_ofReal.comp
              (measurable_const.mul (measurable_id.pow_const a))).mul (hφm.pow_const q)
          have hB : Measurable fun η : ℝ => ψ η ^ q := hψm.pow_const q
          have e1 := lintegral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ)))
            (ν := (volume.restrict (Ico (-c / 2) (c / 2))).prod volume)
            (f := fun s : ℝ => ENNReal.ofReal (c⁻¹ * s ^ a) * φ s ^ q)
            (g := fun w : ℝ × ℝ => ψ w.2 ^ q) hA.aemeasurable
            (hB.comp measurable_snd).aemeasurable
          have e2 := lintegral_prod_mul (μ := volume.restrict (Ico (-c / 2) (c / 2)))
            (ν := volume) (f := fun _ : ℝ => (1 : ℝ≥0∞))
            (g := fun η : ℝ => ψ η ^ q) measurable_const.aemeasurable hB.aemeasurable
          simp only [one_mul] at e2
          simp only [lintegral_const, one_mul, Measure.restrict_apply_univ,
            Real.volume_Ico] at e2
          have hw : c / 2 - (-c / 2) = c := by ring
          rw [hw] at e2
          rw [show (fun x : ℝ × (ℝ × ℝ) => (ENNReal.ofReal (c⁻¹ * x.1 ^ a) * φ x.1 ^ q) *
              ψ x.2.2 ^ q) = fun z => (fun s : ℝ => ENNReal.ofReal (c⁻¹ * s ^ a) * φ s ^ q) z.1 *
              (fun w : ℝ × ℝ => ψ w.2 ^ q) z.2 from rfl, e1, e2]
      _ ≤ ENNReal.ofReal (c⁻¹ * M ^ q * (H / 2) ^ ((21 : ℝ) / 8)) *
            (ENNReal.ofReal c * ENNReal.ofReal (K' * c ^ ((N : ℝ) * q + 1))) := by
          gcongr
          · -- the age integral
            have hpt : ∀ s : ℝ, ENNReal.ofReal (c⁻¹ * s ^ a) * φ s ^ q ≤
                Set.indicator (Ioc 0 (H / 2))
                  (fun _ => ENNReal.ofReal (c⁻¹ * M ^ q * (H / 2) ^ ((13 : ℝ) / 8))) s := by
              intro s
              by_cases hs : s ∈ Ioc 0 (H / 2)
              · rw [indicator_of_mem hs, hφ, indicator_of_mem hs,
                  ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hM hs.1.le) hq0.le,
                  ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hc0.le) (Real.rpow_nonneg hs.1.le _))]
                apply ENNReal.ofReal_le_ofReal
                have hs0 : 0 < s := hs.1
                have h1 : s ^ a * (M * s) ^ q = M ^ q * s ^ ((13 : ℝ) / 8) := by
                  rw [Real.mul_rpow hM hs0.le, ← haq, Real.rpow_add hs0]; ring
                have h2 : s ^ ((13 : ℝ) / 8) ≤ (H / 2) ^ ((13 : ℝ) / 8) :=
                  Real.rpow_le_rpow hs0.le hs.2 (by norm_num)
                calc c⁻¹ * s ^ a * (M * s) ^ q = c⁻¹ * (M ^ q * s ^ ((13 : ℝ) / 8)) := by
                      rw [mul_assoc, h1]
                  _ ≤ c⁻¹ * (M ^ q * (H / 2) ^ ((13 : ℝ) / 8)) := by gcongr
                  _ = _ := by ring
              · rw [indicator_of_notMem hs, hφ, indicator_of_notMem hs]
                have : (0 : ℝ≥0∞) ^ q = 0 := ENNReal.zero_rpow_of_pos hq0
                simp [this]
            calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (c⁻¹ * s ^ a) * φ s ^ q
                ≤ ∫⁻ s in Ioi (0 : ℝ), Set.indicator (Ioc 0 (H / 2))
                  (fun _ => ENNReal.ofReal (c⁻¹ * M ^ q * (H / 2) ^ ((13 : ℝ) / 8))) s :=
                  lintegral_mono hpt
              _ = ENNReal.ofReal (c⁻¹ * M ^ q * (H / 2) ^ ((13 : ℝ) / 8)) *
                    (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 (H / 2)) :=
                  lintegral_indicator_const measurableSet_Ioc _
              _ = ENNReal.ofReal (c⁻¹ * M ^ q * (H / 2) ^ ((13 : ℝ) / 8)) *
                    ENNReal.ofReal (H / 2) := by
                  rw [Measure.restrict_apply measurableSet_Ioc,
                    Set.inter_eq_left.2 Ioc_subset_Ioi_self, Real.volume_Ioc]
                  simp
              _ = ENNReal.ofReal (c⁻¹ * M ^ q * (H / 2) ^ ((21 : ℝ) / 8)) := by
                  rw [← ENNReal.ofReal_mul (by positivity)]
                  congr 1
                  have : (H / 2) ^ ((21 : ℝ) / 8) = (H / 2) ^ ((13 : ℝ) / 8) * (H / 2) := by
                    rw [show (21 : ℝ) / 8 = 13 / 8 + 1 by norm_num,
                      Real.rpow_add (by positivity), Real.rpow_one]
                  rw [this]; ring
          · -- the eta integral
            have hψq : ∀ η : ℝ, ψ η ^ q =
                ENNReal.ofReal ((1 + |η|) ^ ((N : ℝ) * q) * Real.exp (-(q * κ * |η| / c))) := by
              intro η
              rw [hψ, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
              congr 1
              rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.rpow_natCast,
                ← Real.rpow_mul (by positivity), ← Real.exp_mul]
              congr 2; ring
            simp_rw [hψq]
            exact hE c hc
      _ = ENNReal.ofReal (M ^ q * (H / 2) ^ ((21 : ℝ) / 8) * K' * c ^ ((N : ℝ) * q + 1)) := by
          rw [← ENNReal.ofReal_mul hc0.le, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  -- finish
  have hbound : ENNReal.ofReal (M ^ q * (H / 2) ^ ((21 : ℝ) / 8) * K' * c ^ ((N : ℝ) * q + 1)) ≤
      ENNReal.ofReal (K' ^ (1 / q) * M * (1 + H) * c ^ (N + 1)) ^ q := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
    apply ENNReal.ofReal_le_ofReal
    have e1 : (K' ^ (1 / q) * M * (1 + H) * c ^ (N + 1)) ^ q =
        K' * M ^ q * (1 + H) ^ q * c ^ ((N : ℝ) * q + q) := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
        (by positivity), Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hK'.le, one_div, inv_mul_cancel₀ hq0.ne', Real.rpow_one,
        ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
      congr 2
      push_cast; ring
    rw [e1]
    have h1 : (H / 2) ^ ((21 : ℝ) / 8) ≤ (1 + H) ^ q := by
      calc (H / 2) ^ ((21 : ℝ) / 8) ≤ (1 + H) ^ ((21 : ℝ) / 8) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        _ ≤ (1 + H) ^ q := Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hq]; norm_num)
    have h2 : c ^ ((N : ℝ) * q + 1) ≤ c ^ ((N : ℝ) * q + q) :=
      Real.rpow_le_rpow_of_exponent_le hc (by rw [hq]; linarith)
    have hMq : 0 ≤ M ^ q := by positivity
    calc M ^ q * (H / 2) ^ ((21 : ℝ) / 8) * K' * c ^ ((N : ℝ) * q + 1)
        ≤ M ^ q * (1 + H) ^ q * K' * c ^ ((N : ℝ) * q + q) := by gcongr
      _ = _ := by ring
  unfold hNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [bgp]) ENNReal.ofReal_ne_top,
    htr]
  calc (∫⁻ x, ‖f x‖ₑ ^ q ∂(hMeas c bgp)) ^ (1 / q)
      ≤ (ENNReal.ofReal (K' ^ (1 / q) * M * (1 + H) * c ^ (N + 1)) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (hint.trans hbound) (by positivity)
    _ = _ := by rw [one_div]; exact ENNReal.rpow_rpow_inv hq0.ne' _

end UnforcedLeray.Short.IIb

end
