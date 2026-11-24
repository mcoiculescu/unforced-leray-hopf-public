import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14.StressEpsCommutingFlowShiftQ.PhaseLiftBridge

/-!
# Cutoff-shift commutator, `Gamma` bounds, and `cellMeasure` localisation helpers

Shared `lintegral`-to-`cellL2Norm` / `integral` converters, `Gamma` elementary bounds, and
cutoff-shift commutator estimates for `PartII-a:N05/3/2` and `PartII-a:N05/3/1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N05FlowAux

open UnforcedLeray.B0220 UnforcedLeray.B0223

/-! ### 1. Elementary `Gamma` inequalities -/

theorem two_add_H1_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hL1 : 0 ≤ L1) (hγ : 0 < γs) (hM : 0 ≤ M) :
    2 + H1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < ν⁻¹ := inv_pos.2 hν
  have : 0 < c⁻¹ := inv_pos.2 hc
  have : 0 < σ⁻¹ := inv_pos.2 hσ
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]

theorem one_add_H1_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hL1 : 0 ≤ L1) (hγ : 0 < γs) (hM : 0 ≤ M) :
    1 + H1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  linarith [two_add_H1_le_gamma (H1 := H1) χ χ1 hν hc hσ hL1 hγ hM]

theorem one_add_L1_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hγ : 0 < γs) (hM : 0 ≤ M) :
    1 + L1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < H1 := lt_of_lt_of_le hσ hσH
  have : 0 < ν⁻¹ := inv_pos.2 hν
  have : 0 < c⁻¹ := inv_pos.2 hc
  have : 0 < σ⁻¹ := inv_pos.2 hσ
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]

theorem one_add_inv_sigma_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1)
    (hγ : 0 < γs) (hM : 0 ≤ M) :
    1 + σ⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < H1 := lt_of_lt_of_le hσ hσH
  have : 0 < ν⁻¹ := inv_pos.2 hν
  have : 0 < c⁻¹ := inv_pos.2 hc
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]

theorem inv_sigma_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1)
    (hγ : 0 < γs) (hM : 0 ≤ M) :
    σ⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  linarith [one_add_inv_sigma_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM]

theorem inv_sqrt_sigma_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1)
    (hγ : 0 < γs) (hM : 0 ≤ M) :
    (Real.sqrt σ)⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ Gam := N05_1Aux.one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hσi : σ⁻¹ ≤ Gam := inv_sigma_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM
  have hsq : ((Real.sqrt σ)⁻¹) ^ 2 ≤ Gam ^ 2 := by
    rw [inv_pow, Real.sq_sqrt hσ.le]
    calc σ⁻¹
        ≤ Gam := hσi
      _ ≤ Gam ^ 2 := by nlinarith
  exact (abs_le_of_sq_le_sq' hsq hG0).2

theorem cNorm8_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1)
    (hγ : 0 < γs) (hM : 0 ≤ M) :
    cNorm8 χ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < H1 := lt_of_lt_of_le hσ hσH
  have : 0 < ν⁻¹ := inv_pos.2 hν
  have : 0 < c⁻¹ := inv_pos.2 hc
  have : 0 < σ⁻¹ := inv_pos.2 hσ
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  linarith [cNorm8_nonneg χ1]

/-! ### 2. Real exponential Lipschitz bound and cutoff MVT -/

theorem abs_exp_sub_one_le {x R : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) :
    |Real.exp x - 1| ≤ Real.exp R * |x| := by
  have hx_mem : x ∈ Icc (-R) R := abs_le.1 hx
  have h0_mem : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR⟩
  have hmvt := (convex_Icc (-R) R).norm_image_sub_le_of_norm_deriv_le
    (fun y _ => Real.differentiableAt_exp)
    (fun y hy => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
      exact Real.exp_le_exp.2 hy.2)
    h0_mem hx_mem
  simpa [Real.norm_eq_abs] using hmvt

theorem abs_cutoff_sub_le {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p q : Profile) :
    |χ q - χ p| ≤ cNorm8 χ * ‖q - p‖ := by
  have hd : ∀ r ∈ (univ : Set Profile), DifferentiableAt ℝ χ r :=
    fun r _ => (hχ.smooth.differentiable (by decide)) r
  have hbd : ∀ r ∈ (univ : Set Profile), ‖fderiv ℝ χ r‖ ≤ cNorm8 χ :=
    fun r _ => N05_3_1Aux.norm_fderiv_le_cNorm8_of_nearCutoff hc hχ r
  have hmvt := convex_univ.norm_image_sub_le_of_norm_fderiv_le hd hbd (mem_univ p) (mem_univ q)
  rwa [Real.norm_eq_abs] at hmvt

theorem norm_shiftQ_sub (h : ℝ) (p : Profile) : ‖shiftQ h p - p‖ = |h| := by
  have heq : shiftQ h p - p = ((0 : ℝ), h, (0 : ℝ)) := by
    rcases p with ⟨s, q, η⟩
    ext <;> simp [shiftQ]
  rw [heq]
  simp [Prod.norm_def, Real.norm_eq_abs]

theorem norm_shiftEta_sub (h : ℝ) (p : Profile) : ‖shiftEta h p - p‖ = |h| := by
  have heq : shiftEta h p - p = ((0 : ℝ), (0 : ℝ), h) := by
    rcases p with ⟨s, q, η⟩
    ext <;> simp [shiftEta]
  rw [heq]
  simp [Prod.norm_def, Real.norm_eq_abs]

theorem norm_shiftS_sub (h : ℝ) (p : Profile) : ‖shiftS h p - p‖ = |h| := by
  have heq : shiftS h p - p = (h, (0 : ℝ), (0 : ℝ)) := by
    rcases p with ⟨s, q, η⟩
    ext <;> simp [shiftS]
  rw [heq]
  simp [Prod.norm_def, Real.norm_eq_abs]

/-! ### 3. `cellMeasure` / `measureH` localisation and `lintegral`-to-`integral` bridges -/

theorem lintegral_periodize_sq_eq_ofReal_norm_sq {c : ℝ} (hc : 0 < c) (W : HSpace c MeridC) :
    ∫⁻ p, ‖periodize c (W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
      ENNReal.ofReal (‖W‖ ^ 2) := by
  have hcongr : ∫⁻ p, ‖periodize c (W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
      ∫⁻ p, ‖(W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_cell_measureH c] with p hpcell
    rw [periodize_of_mem hc (W : Profile → MeridC) hpcell]
  rw [hcongr]
  exact lintegral_enorm_sq_eq_ofReal_norm_sq W

private theorem one_le_one_add_sq_mul_weightH {σ' H1' : ℝ} (hσ' : 0 < σ') (hσH' : σ' ≤ H1')
    {p : Profile} (hs1 : σ' ≤ p.1) (hs2 : p.1 ≤ H1') :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + H1') ^ 2) * weightH p := by
  have hs_pos : 0 < p.1 := lt_of_lt_of_le hσ' hs1
  have hH1'_pos : 0 < H1' := lt_of_lt_of_le hσ' hσH'
  have h1H1 : 1 ≤ 1 + H1' := by linarith
  have hp1H1 : p.1 ≤ 1 + H1' := by linarith
  have hrpow : p.1 ^ (3 / 2 : ℝ) ≤ (1 + H1') ^ 2 := by
    calc p.1 ^ (3 / 2 : ℝ)
        ≤ (1 + H1') ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hs_pos.le hp1H1 (by norm_num)
      _ ≤ (1 + H1') ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1H1 (by norm_num)
      _ = (1 + H1') ^ 2 := Real.rpow_two (1 + H1')
  have h1 : 1 ≤ (1 + H1') ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) := by
    calc (1 : ℝ)
        = p.1 ^ (3 / 2 : ℝ) * p.1 ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hs_pos]; norm_num
      _ ≤ (1 + H1') ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hs_pos.le _)
  unfold weightH
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal h1

/-- Localises `∫⁻ p, ‖ψ p • g p‖ₑ ^ 2 ∂(cellMeasure c)` to `profileBox σ' H1' L1'` against
`measureH c`. -/
theorem lintegral_cutoff_smul_sq_le_profileBox {c σ' H1' L1' B : ℝ}
    (hσ' : 0 < σ') (hσH' : σ' ≤ H1')
    {ψ : Profile → ℝ} (hψ_bd : ∀ p, |ψ p| ≤ B)
    (hψ_supp : ∀ p, ψ p ≠ 0 → p ∈ profileBox σ' H1' L1')
    {g : Profile → MeridC} (hg : Measurable g) :
    ∫⁻ p, ‖ψ p • g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1') * B) ^ 2) *
        ∫⁻ p in profileBox σ' H1' L1', ‖g p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
  have hmB : MeasurableSet (profileBox σ' H1' L1') := measurableSet_profileBox σ' H1' L1'
  have hind_meas : Measurable
      ((profileBox σ' H1' L1').indicator (fun p : Profile => ‖g p‖ₑ ^ (2 : ℝ))) :=
    (hg.enorm.pow_const (2 : ℝ)).indicator hmB
  have hpt : ∀ p : Profile,
      ‖ψ p • g p‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (((1 + H1') * B) ^ 2) *
          (weightH p *
            (profileBox σ' H1' L1').indicator (fun q : Profile => ‖g q‖ₑ ^ (2 : ℝ)) p) := by
    intro p
    by_cases hψ0 : ψ p = 0
    · simp [hψ0]
    · have hpB : p ∈ profileBox σ' H1' L1' := hψ_supp p hψ0
      have hw := one_le_one_add_sq_mul_weightH hσ' hσH' hpB.1 hpB.2.1
      have hsmul_le : ‖ψ p • g p‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (B ^ 2) * ‖g p‖ₑ ^ (2 : ℝ) := by
        have hnorm : ‖ψ p • g p‖ ≤ B * ‖g p‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hψ_bd p) (norm_nonneg _)
        have hsq : ‖ψ p • g p‖ ^ 2 ≤ B ^ 2 * ‖g p‖ ^ 2 := by
          calc ‖ψ p • g p‖ ^ 2 ≤ (B * ‖g p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
            _ = B ^ 2 * ‖g p‖ ^ 2 := mul_pow _ _ _
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          Real.rpow_two, ← ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two,
          ← ENNReal.ofReal_mul (sq_nonneg B)]
        exact ENNReal.ofReal_le_ofReal hsq
      rw [indicator_of_mem hpB]
      calc ‖ψ p • g p‖ₑ ^ (2 : ℝ)
          ≤ ENNReal.ofReal (B ^ 2) * (1 * ‖g p‖ₑ ^ (2 : ℝ)) := by simpa using hsmul_le
        _ ≤ ENNReal.ofReal (B ^ 2) *
              ((ENNReal.ofReal ((1 + H1') ^ 2) * weightH p) * ‖g p‖ₑ ^ (2 : ℝ)) := by gcongr
        _ = (ENNReal.ofReal ((1 + H1') ^ 2) * ENNReal.ofReal (B ^ 2)) *
              (weightH p * ‖g p‖ₑ ^ (2 : ℝ)) := by
              rw [mul_assoc (ENNReal.ofReal ((1 + H1') ^ 2)), ← mul_assoc,
                mul_comm (ENNReal.ofReal (B ^ 2))]
        _ = ENNReal.ofReal (((1 + H1') * B) ^ 2) * (weightH p * ‖g p‖ₑ ^ (2 : ℝ)) := by
              rw [← ENNReal.ofReal_mul (sq_nonneg _)]
              congr 1
              ring
  calc ∫⁻ p, ‖ψ p • g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ∫⁻ p, ENNReal.ofReal (((1 + H1') * B) ^ 2) *
          (weightH p *
            (profileBox σ' H1' L1').indicator (fun q : Profile => ‖g q‖ₑ ^ (2 : ℝ)) p)
          ∂(cellMeasure c) := lintegral_mono hpt
    _ = ENNReal.ofReal (((1 + H1') * B) ^ 2) *
          ∫⁻ p, weightH p *
            (profileBox σ' H1' L1').indicator (fun q : Profile => ‖g q‖ₑ ^ (2 : ℝ)) p
          ∂(cellMeasure c) :=
        lintegral_const_mul _ (measurable_weightH.mul hind_meas)
    _ = ENNReal.ofReal (((1 + H1') * B) ^ 2) *
          ∫⁻ p, (profileBox σ' H1' L1').indicator (fun q : Profile => ‖g q‖ₑ ^ (2 : ℝ)) p
          ∂(measureH c) := by
        rw [measureH, lintegral_withDensity_eq_lintegral_mul _ measurable_weightH hind_meas]
        rfl
    _ = ENNReal.ofReal (((1 + H1') * B) ^ 2) *
          ∫⁻ p in profileBox σ' H1' L1', ‖g p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
        rw [lintegral_indicator hmB]

/-- Bounds `∫⁻ p, ‖flatStressCutRep c ψ W p‖ₑ ^ 2 ∂(cellMeasure c)` for any bounded measurable
multiplier `ψ` supported in `σ' ≤ p.1 ≤ H1'`. -/
theorem lintegral_bounded_smul_periodize_sq_le {c σ' H1' B : ℝ}
    (hc : 0 < c) (hσ' : 0 < σ') (hσH' : σ' ≤ H1')
    {ψ : Profile → ℝ} (hψ_m : Measurable ψ) (hψ_bd : ∀ p, |ψ p| ≤ B)
    (hψ_supp : ∀ p, ψ p ≠ 0 → σ' ≤ p.1 ∧ p.1 ≤ H1')
    (W : HSpace c MeridC) :
    ∫⁻ p, ‖flatStressCutRep c ψ W p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1') * B * ‖W‖) ^ 2) := by
  let u := flatStressCutRep c ψ W
  have hu : Measurable u := N05_4Aux.measurable_flatStressCutRep c hψ_m W
  have hstep1 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((1 + H1') ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
    have hpt : ∀ p : Profile,
        ‖u p‖ₑ ^ (2 : ℝ) ≤
          ENNReal.ofReal ((1 + H1') ^ 2) * (weightH p * ‖u p‖ₑ ^ (2 : ℝ)) := by
      intro p
      by_cases hp0 : ψ p = 0
      · simp [u, flatStressCutRep, hp0]
      · obtain ⟨hs1, hs2⟩ := hψ_supp p hp0
        have hw := one_le_one_add_sq_mul_weightH hσ' hσH' hs1 hs2
        calc ‖u p‖ₑ ^ (2 : ℝ)
            = 1 * ‖u p‖ₑ ^ (2 : ℝ) := (one_mul _).symm
          _ ≤ (ENNReal.ofReal ((1 + H1') ^ 2) * weightH p) * ‖u p‖ₑ ^ (2 : ℝ) := by gcongr
          _ = ENNReal.ofReal ((1 + H1') ^ 2) * (weightH p * ‖u p‖ₑ ^ (2 : ℝ)) := mul_assoc _ _ _
    calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal ((1 + H1') ^ 2) * (weightH p * ‖u p‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal ((1 + H1') ^ 2) *
            ∫⁻ p, weightH p * ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_const_mul _ (measurable_weightH.mul (hu.enorm.pow_const (2 : ℝ)))
      _ = ENNReal.ofReal ((1 + H1') ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
          rw [measureH, lintegral_withDensity_eq_lintegral_mul _
            measurable_weightH (hu.enorm.pow_const (2 : ℝ))]
          rfl
  let U₀ := mulChi (measureH c) ψ hψ_m hψ_bd W
  have hae : (U₀ : Profile → MeridC) =ᵐ[measureH c] u :=
    N05_4Aux.flatStressCutRep_ae_eq hc ψ hψ_m hψ_bd W
  have hU0_norm : ‖U₀‖ ≤ B * ‖W‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_chi_smul (measureH c) ψ hψ_m hψ_bd (Lp.memLp W)).coeFn_toLp] with p hp
    change ‖((memLp_chi_smul (measureH c) ψ hψ_m hψ_bd (Lp.memLp W)).toLp _) p‖ ≤ _
    rw [hp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hψ_bd p) (norm_nonneg _)
  have hstep2 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) ≤ ENNReal.ofReal ((B * ‖W‖) ^ 2) := by
    have hcongr : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ∫⁻ p, ‖(U₀ : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with p hp
      rw [hp]
    rw [hcongr, lintegral_enorm_sq_eq_ofReal_norm_sq U₀]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg U₀) hU0_norm 2)
  calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ENNReal.ofReal ((1 + H1') ^ 2) * ENNReal.ofReal ((B * ‖W‖) ^ 2) :=
        hstep1.trans (by gcongr)
    _ = ENNReal.ofReal (((1 + H1') * B * ‖W‖) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        ring

/-- Splits `‖flatStressCutRep c χ W (shift p) - flatStressCutRep c χ W p‖ₑ ^ 2` into the shifted-`b`
term and the cutoff-commutator term. -/
theorem lintegral_flatStressCutRep_shift_sub_sq_le_split {c : ℝ}
    {χ : Profile → ℝ} (hm : Measurable χ)
    {shift : Profile → Profile} (hshift : Measurable shift)
    (W : HSpace c MeridC) :
    ∫⁻ p, ‖flatStressCutRep c χ W (shift p) - flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ)
        ∂(cellMeasure c) ≤
      2 * ∫⁻ p, ‖χ (shift p) •
          (periodize c (W : Profile → MeridC) (shift p) -
            periodize c (W : Profile → MeridC) p)‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) +
      2 * ∫⁻ p, ‖flatStressCutRep c (fun q => χ (shift q) - χ q) W p‖ₑ ^ (2 : ℝ)
        ∂(cellMeasure c) := by
  have hb_meas : Measurable (periodize c (W : Profile → MeridC)) :=
    measurable_periodize_any c (Lp.stronglyMeasurable W).measurable
  have hm1 : Measurable fun p : Profile =>
      ‖χ (shift p) •
        (periodize c (W : Profile → MeridC) (shift p) -
          periodize c (W : Profile → MeridC) p)‖ₑ ^ (2 : ℝ) :=
    ((hm.comp hshift).smul ((hb_meas.comp hshift).sub hb_meas)).enorm.pow_const _
  have hm2 : Measurable fun p : Profile =>
      ‖flatStressCutRep c (fun q => χ (shift q) - χ q) W p‖ₑ ^ (2 : ℝ) :=
    (N05_4Aux.measurable_flatStressCutRep c ((hm.comp hshift).sub hm) W).enorm.pow_const _
  have hpt : ∀ p : Profile,
      ‖flatStressCutRep c χ W (shift p) - flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ) ≤
        2 * ‖χ (shift p) •
            (periodize c (W : Profile → MeridC) (shift p) -
              periodize c (W : Profile → MeridC) p)‖ₑ ^ (2 : ℝ) +
        2 * ‖flatStressCutRep c (fun q => χ (shift q) - χ q) W p‖ₑ ^ (2 : ℝ) := by
    intro p
    let a : MeridC := χ (shift p) •
      (periodize c (W : Profile → MeridC) (shift p) - periodize c (W : Profile → MeridC) p)
    let d : MeridC := flatStressCutRep c (fun q => χ (shift q) - χ q) W p
    have hdecomp : flatStressCutRep c χ W (shift p) - flatStressCutRep c χ W p = a + d := by
      dsimp only [flatStressCutRep, a, d]
      rw [smul_sub, sub_smul]
      abel
    have hreal : ‖a + d‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖d‖ ^ 2 := by
      have htri : ‖a + d‖ ≤ ‖a‖ + ‖d‖ := norm_add_le a d
      have hsq : ‖a + d‖ ^ 2 ≤ (‖a‖ + ‖d‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [sq_nonneg (‖a‖ - ‖d‖)]
    rw [hdecomp]
    have h1 : ‖a + d‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖a + d‖ ^ 2) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    have h2 : 2 * ‖a‖ₑ ^ (2 : ℝ) + 2 * ‖d‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (2 * ‖a‖ ^ 2 + 2 * ‖d‖ ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat, ← ofReal_norm, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two, Real.rpow_two]
    change ‖a + d‖ₑ ^ (2 : ℝ) ≤ 2 * ‖a‖ₑ ^ (2 : ℝ) + 2 * ‖d‖ₑ ^ (2 : ℝ)
    rw [h1, h2]
    exact ENNReal.ofReal_le_ofReal hreal
  calc ∫⁻ p, ‖flatStressCutRep c χ W (shift p) - flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ)
          ∂(cellMeasure c)
      ≤ ∫⁻ p, (2 * ‖χ (shift p) •
            (periodize c (W : Profile → MeridC) (shift p) -
              periodize c (W : Profile → MeridC) p)‖ₑ ^ (2 : ℝ) +
          2 * ‖flatStressCutRep c (fun q => χ (shift q) - χ q) W p‖ₑ ^ (2 : ℝ))
          ∂(cellMeasure c) := lintegral_mono hpt
    _ = 2 * ∫⁻ p, ‖χ (shift p) •
            (periodize c (W : Profile → MeridC) (shift p) -
              periodize c (W : Profile → MeridC) p)‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) +
        2 * ∫⁻ p, ‖flatStressCutRep c (fun q => χ (shift q) - χ q) W p‖ₑ ^ (2 : ℝ)
          ∂(cellMeasure c) := by
        rw [lintegral_add_left (hm1.const_mul 2),
          lintegral_const_mul 2 hm1, lintegral_const_mul 2 hm2]

/-- Converts an `ENNReal.ofReal R` bound on `∫⁻ p, ‖f p‖ₑ ^ 2 ∂μ` into a Bochner integral bound
`∫ p, ‖f p‖ ^ 2 ∂μ ≤ R`. -/
theorem integral_norm_sq_le_of_lintegral_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {f : α → E} (hf : Measurable f)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hlint : ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal R) :
    ∫ p, ‖f p‖ ^ 2 ∂μ ≤ R := by
  have hmem : MemLp f 2 μ := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (lt_of_le_of_lt hlint ENNReal.ofReal_lt_top).ne
  have hint : Integrable (fun p => ‖f p‖ ^ 2) μ := hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖f p‖ ^ 2 ∂μ) = ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  exact (ENNReal.ofReal_le_ofReal_iff hR0).1 (hofReal.trans_le hlint)

/-- Converts an `ENNReal.ofReal (B ^ 2)` bound on `∫⁻ p, ‖f p‖ₑ ^ 2 ∂(cellMeasure c)` into
`cellL2Norm c f ≤ B`. -/
theorem cellL2Norm_le_of_lintegral_le {c B : ℝ} (hB0 : 0 ≤ B)
    {f : Profile → MeridC} (hf : Measurable f)
    (hlint : ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤ ENNReal.ofReal (B ^ 2)) :
    cellL2Norm c f ≤ B := by
  have hint_le := integral_norm_sq_le_of_lintegral_le hf (sq_nonneg B) hlint
  unfold cellL2Norm
  calc (∫ p, ‖f p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (B ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = B := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hB0]

end UnforcedLeray.Short.PartIIa.N05FlowAux
