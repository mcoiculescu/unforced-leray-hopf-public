import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Pointwise.Entry

/-!
# `OscFarPt` (task `PartIII-b:C/rep/8/1/1/1/2/1/4`)

Source `the November 2 reference manuscript`
lines 5400-5427, 3768-3790.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

open UnforcedLeray UnforcedLeray.Short.IIIa

lemma clm_enorm_le {L : Space →L[ℝ] (Fin 3 → ℂ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h : ∀ (w : Space) (i : Fin 3), ‖w‖ ≤ 1 → ‖L w i‖ₑ ≤ M) : ‖L‖ₑ ≤ M := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_toReal hM]
  refine ENNReal.ofReal_le_ofReal (L.opNorm_le_bound ENNReal.toReal_nonneg fun v => ?_)
  by_cases hv : ‖v‖ = 0
  · simp [norm_eq_zero.1 hv]
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    set w := ‖v‖⁻¹ • v
    have hw : ‖w‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hvpos.le), inv_mul_cancel₀ hv]
    have hLw : ‖L w‖ ≤ M.toReal := by
      refine (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2 fun i => ?_
      have hi := h w i hw
      rw [← ofReal_norm_eq_enorm] at hi
      exact (ENNReal.ofReal_le_iff_le_toReal hM).1 hi
    have hv_eq : v = ‖v‖ • w := by simp [w, smul_smul, mul_inv_cancel₀ hv]
    calc ‖L v‖ = ‖L (‖v‖ • w)‖ := by rw [← hv_eq]
      _ = ‖v‖ * ‖L w‖ := by rw [L.map_smul, norm_smul, Real.norm_of_nonneg hvpos.le]
      _ ≤ ‖v‖ * M.toReal := mul_le_mul_of_nonneg_left hLw hvpos.le
      _ = M.toReal * ‖v‖ := mul_comm _ _

lemma thin_z_moment_le {ε c ρo : ℝ} {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hε : 0 < ε) (hc : 0 < c) (h : ThinHyp c ρo F) :
    ∫⁻ z : Space, ENNReal.ofReal (1 + |z 2|) *
        ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) ≤
      ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * thinMoment c F) := by
  let φ : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (1 + |w.2|) * ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F w.1 w.2 q))
  have h1 : (∫⁻ z : Space, ENNReal.ofReal (1 + |z 2|) *
      ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) =
      ∫⁻ z : Space, φ ((ε * z 0, ε * z 1), z 2) := rfl
  rw [h1, lintegral_space_scale hε φ]
  refine mul_le_mul_right ?_ _
  unfold thinMoment
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun w => ?_
  have hcs := cs_phase c hc (fun q => tensorNorm (F w.1 w.2 q)) (tn_meas_phase h w.1 w.2)
    (fun _ => Real.sqrt_nonneg _)
  calc φ w ≤ ENNReal.ofReal (1 + |w.2|) *
        (ENNReal.ofReal c * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ *
          ENNReal.ofReal (tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_right hcs _
    _ = _ := by ring

lemma thinSource_q0_apply {ε : ℝ} (hε : 0 < ε) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (τ l : ℝ) (z : Space) (j₀ k₀ : Fin 3) :
    thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ =
      F (ε * z 0, ε * z 1) (z 2) (q0 ε τ z + ε⁻¹ * Real.log l) j₀ k₀ := by
  unfold thinSource q0
  have heq : ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + (τ + 2 * Real.log l) / (2 * ε) =
      (ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + τ / (2 * ε)) + ε⁻¹ * Real.log l := by
    field_simp
    ring
  rw [heq]

set_option maxHeartbeats 800000 in
theorem oscFarPt : UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg.OscFarPt := by
  intro K hK hRe
  obtain ⟨C₀, m, hC₀, hOsc⟩ := oscPoint K hK hRe
  refine ⟨18 * C₀, m + 1, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ F hmeas hper hsupp hzero hN xo hxo τ
  have hth : ThinHyp c ρo F := ⟨hmeas, hper, hsupp⟩
  set y0 : Space := ε⁻¹ • xo
  set r : ℝ := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  set B : ℝ := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hrpos : 0 < r := lt_of_lt_of_le hρi hxo
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := mul_nonneg hρi.le (inv_nonneg.2 (by linarith))
    positivity
  have hcB : c ≤ B := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := mul_nonneg hρi.le (inv_nonneg.2 (by linarith))
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have : 0 ≤ ρi⁻¹ := inv_nonneg.2 hρi.le
    change c ≤ 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
    linarith
  have hy0 : ρi / ε ≤ Real.sqrt (y0 0 ^ 2 + y0 1 ^ 2) := by
    change ρi / ε ≤ hor (ε⁻¹ • xo)
    rw [hor_smul _ (inv_nonneg.2 hε.le), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  have hP : 0 < 2 * ε * c := by positivity
  have hDomF : sepDom (2 * μ.re + 2) 0 (ρi / ε - ρo / ε) (srcNorm (thinSource ε F)) τ y0 < ⊤ :=
    sepDom_thin_lt_top hε hc hρ (hRe μ hμ) hth hN τ y0
  obtain ⟨hIntF, hHasF⟩ := fderiv_sepW_of hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth) τ y0 hy0 hDomF
  have hIntE : ∀ j₀ k₀ : Fin 3,
      Integrable (fun p => fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0)
        sepDiffRho := by
    intro j₀ k₀
    have hNE : thinMoment c (entryF j₀ k₀ F) ≠ ⊤ :=
      ne_top_of_le_ne_top hN (thinMoment_entryF_le c F j₀ k₀)
    have hDomE := sepDom_thin_lt_top hε hc hρ (hRe μ hμ) (thinHyp_entryF hth j₀ k₀) hNE τ y0
    exact (fderiv_sepW_of hν (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) hP
      (thin_isSep hε (thinHyp_entryF hth j₀ k₀)) τ y0 hy0 hDomE).1
  -- Bound each `(j₀, k₀)` integral at direction `w` and component `i`
  have hEntryBound : ∀ (j₀ k₀ : Fin 3) (w : Space) (i : Fin 3), ‖w‖ ≤ 1 →
      ‖((∫ p, fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 ∂sepDiffRho) w) i‖ₑ ≤
        ENNReal.ofReal (2 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ)) * thinMoment c F := by
    intro j₀ k₀ w i hw
    let Λ : (Space →L[ℝ] (Fin 3 → ℂ)) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
        (ContinuousLinearMap.apply ℝ (Fin 3 → ℂ) w)
    have hΛInt : Integrable (fun p =>
        (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 w) i) sepDiffRho :=
      Λ.integrable_comp (hIntE j₀ k₀)
    have hΛEq : ((∫ p, fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0
        ∂sepDiffRho) w) i =
        ∫ z : Space, ∫ l in Ioo (0 : ℝ) 1,
          (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 w) i := by
      have h1 := (Λ.integral_comp_comm (hIntE j₀ k₀)).symm
      simp only [Λ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.apply_apply] at h1
      rw [h1]
      exact integral_prod_symm _ hΛInt
    rw [hΛEq]
    have hSlice : ∀ z : Space,
        ‖∫ l in Ioo (0 : ℝ) 1,
            (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 w) i‖ₑ ≤
          ENNReal.ofReal (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) *
            (ENNReal.ofReal (1 + |z 2|) *
              ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) := by
      intro z
      have hcongr : (∫ l in Ioo (0 : ℝ) 1,
          (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 w) i) =
          (-2 : ℂ) * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
            ((fderiv ℝ (fun y' => fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j₀ x)
              (y' - l • z) (UnforcedLeray.coordinateVector k₀)) y0 w : ℝ) : ℂ) *
            ((F (ε * z 0, ε * z 1) (z 2) (q0 ε τ z + ε⁻¹ * Real.log l) j₀ k₀ : ℝ) : ℂ) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun l hl => ?_
        rw [fderiv_sepDiffF_entryF hν ε μ F τ j₀ k₀ hl z y0 w i,
          thinSource_q0_apply hε F τ l z j₀ k₀]
      rw [hcongr, enorm_mul]
      have h2 : ‖(-2 : ℂ)‖ₑ = ENNReal.ofReal 2 := by
        rw [← ofReal_norm_eq_enorm]; norm_num
      rw [h2]
      by_cases hz : ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ ρo
      · have hfm : Measurable (fun q => F (ε * z 0, ε * z 1) (z 2) q j₀ k₀) :=
          (hmeas j₀ k₀).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
        have hpt := hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ
          (fun q => F (ε * z 0, ε * z 1) (z 2) q j₀ k₀) hfm
          (fun q => by rw [hper]) (hzero (ε * z 0, ε * z 1) (z 2) j₀ k₀)
          z xo (q0 ε τ z) hz hxo i j₀ k₀ w hw
        have hle_q : (∫⁻ q in Ioc 0 c, ‖F (ε * z 0, ε * z 1) (z 2) q j₀ k₀‖ₑ) ≤
            ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) := by
          refine lintegral_mono fun q => ?_
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (l5_abs_le_tensorNorm _ j₀ k₀)
        calc ENNReal.ofReal 2 * _
            ≤ ENNReal.ofReal 2 *
                (ENNReal.ofReal (C₀ * B ^ m * ε ^ 6 * (1 + |z 2|) * r ^ (-5 : ℝ)) *
                  ∫⁻ q in Ioc 0 c,
                    ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) :=
              mul_le_mul_right (hpt.trans (mul_le_mul_right hle_q _)) _
          _ = _ := by
              have hpos1 : 0 ≤ 2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ) := by positivity
              have hpos2 : 0 ≤ 1 + |z 2| := by positivity
              have heq : ENNReal.ofReal 2 *
                  ENNReal.ofReal (C₀ * B ^ m * ε ^ 6 * (1 + |z 2|) * r ^ (-5 : ℝ)) =
                  ENNReal.ofReal (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) *
                    ENNReal.ofReal (1 + |z 2|) := by
                rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hpos1]
                congr 1; ring
              rw [← mul_assoc, heq, mul_assoc]
      · push Not at hz
        have hF0 : ∀ q, F (ε * z 0, ε * z 1) (z 2) q = 0 := by
          intro q
          apply hsupp
          have : Real.sqrt ((ε * z 0) ^ 2 + (ε * z 1) ^ 2) = ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
            rw [show (ε * z 0) ^ 2 + (ε * z 1) ^ 2 = ε ^ 2 * (z 0 ^ 2 + z 1 ^ 2) by ring,
              Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]
          rw [this]; exact hz
        simp [hF0]
    calc ‖∫ z : Space, ∫ l in Ioo (0 : ℝ) 1,
            (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 w) i‖ₑ
        ≤ ∫⁻ z : Space, ‖∫ l in Ioo (0 : ℝ) 1,
            (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 w) i‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z : Space, ENNReal.ofReal (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) *
            (ENNReal.ofReal (1 + |z 2|) *
              ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) :=
          lintegral_mono hSlice
      _ = ENNReal.ofReal (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) *
            ∫⁻ z : Space, ENNReal.ofReal (1 + |z 2|) *
              ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) *
            (ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * thinMoment c F)) :=
          mul_le_mul_right (thin_z_moment_le hε hc hth) _
      _ ≤ ENNReal.ofReal (2 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ)) * thinMoment c F := by
          rw [← mul_assoc, ← mul_assoc]
          refine mul_le_mul_left ?_ _
          rw [← ENNReal.ofReal_pow (inv_nonneg.2 hε.le),
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hε6 : ε ^ 6 * (ε⁻¹) ^ 2 = ε ^ 4 := by
            have : ε ≠ 0 := hε.ne'
            field_simp
          have h1 : 2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ) * (ε⁻¹) ^ 2 * c =
              2 * C₀ * (B ^ m * c) * ε ^ 4 * r ^ (-5 : ℝ) := by
            calc 2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ) * (ε⁻¹) ^ 2 * c
                = 2 * C₀ * B ^ m * (ε ^ 6 * (ε⁻¹) ^ 2) * r ^ (-5 : ℝ) * c := by ring
              _ = 2 * C₀ * (B ^ m * c) * ε ^ 4 * r ^ (-5 : ℝ) := by rw [hε6]; ring
          have hBm : B ^ m * c ≤ B ^ (m + 1) := by
            rw [pow_succ]
            exact mul_le_mul_of_nonneg_left hcB (pow_nonneg hB0 m)
          rw [h1]
          gcongr
  -- Sum over the 9 `(j₀, k₀)` entries and apply `clm_enorm_le`
  rw [hHasF.fderiv]
  have hSumInt : (∫ p, fderiv ℝ (sepDiffF ν μ (thinSource ε F) τ p) y0 ∂sepDiffRho) =
      ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        ∫ p, fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 ∂sepDiffRho := by
    have hae : ∀ᵐ p ∂sepDiffRho, fderiv ℝ (sepDiffF ν μ (thinSource ε F) τ p) y0 =
        ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
          fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 := by
      filter_upwards [sepDiffRho_ae_mem] with p hp using fderiv_sepDiffF_sum_entryF hν ε μ F τ hp y0
    rw [integral_congr_ae hae,
      integral_finset_sum _ fun j₀ _ => integrable_finset_sum _ fun k₀ _ => hIntE j₀ k₀]
    refine Finset.sum_congr rfl fun j₀ _ => ?_
    exact integral_finset_sum _ fun k₀ _ => hIntE j₀ k₀
  rw [hSumInt]
  have hM_ne_top : ENNReal.ofReal (18 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ)) *
      thinMoment c F ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
  refine clm_enorm_le hM_ne_top fun w i hw => ?_
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  calc ‖∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
          ((∫ p, fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 ∂sepDiffRho) w) i‖ₑ
      ≤ ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
          ‖((∫ p, fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 ∂sepDiffRho) w) i‖ₑ := by
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j₀ _ => ?_)
        exact enorm_sum_le _ _
    _ ≤ ∑ _j₀ : Fin 3, ∑ _k₀ : Fin 3,
          ENNReal.ofReal (2 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ)) * thinMoment c F :=
        Finset.sum_le_sum fun j₀ _ => Finset.sum_le_sum fun k₀ _ => hEntryBound j₀ k₀ w i hw
    _ = ENNReal.ofReal (18 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ)) * thinMoment c F := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        have h9 : ((3 : ℕ) : ℝ≥0∞) * ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 9 := by norm_num
        rw [h9, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
end
