import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1P

/-- General cut-off representative `g • periodize W`. -/
def cutRep (c : ℝ) (g : Profile → ℝ) (W : HSpace c MeridC) (p : Profile) : MeridC :=
  g p • periodize c (W : Profile → MeridC) p

theorem measurable_cutRep (c : ℝ) {g : Profile → ℝ} (hm : Measurable g) (W : HSpace c MeridC) :
    Measurable (cutRep c g W) := N05_4Aux.measurable_flatStressCutRep c hm W

theorem cutRep_enorm_sq_le {c σ H1 : ℝ} (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hs : ∀ p, χ p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1) (W : HSpace c MeridC) (p : Profile) :
    ‖cutRep c χ W p‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal ((1 + H1) ^ 2) * (weightH p * ‖cutRep c χ W p‖ₑ ^ (2 : ℝ)) := by
  by_cases hp0 : cutRep c χ W p = 0
  · simp [hp0]
  · have hg : χ p ≠ 0 := by intro h; apply hp0; simp [cutRep, h]
    obtain ⟨hs1, hs2⟩ := hs p hg
    have hs_pos : 0 < p.1 := lt_of_lt_of_le hσ hs1
    have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
    have h1H1 : 1 ≤ 1 + H1 := by linarith
    have hp1H1 : p.1 ≤ 1 + H1 := by linarith
    have hrpow : p.1 ^ (3 / 2 : ℝ) ≤ (1 + H1) ^ 2 := by
      calc p.1 ^ (3 / 2 : ℝ)
          ≤ (1 + H1) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hs_pos.le hp1H1 (by norm_num)
        _ ≤ (1 + H1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1H1 (by norm_num)
        _ = (1 + H1) ^ 2 := Real.rpow_two (1 + H1)
    have h1 : 1 ≤ (1 + H1) ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) := by
      calc (1 : ℝ)
          = p.1 ^ (3 / 2 : ℝ) * p.1 ^ (-(3 / 2 : ℝ)) := by
            rw [← Real.rpow_add hs_pos]; norm_num
        _ ≤ (1 + H1) ^ 2 * p.1 ^ (-(3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hs_pos.le _)
    have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + H1) ^ 2) * weightH p := by
      unfold weightH
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal h1
    calc ‖cutRep c χ W p‖ₑ ^ (2 : ℝ)
        = 1 * ‖cutRep c χ W p‖ₑ ^ (2 : ℝ) := (one_mul _).symm
      _ ≤ (ENNReal.ofReal ((1 + H1) ^ 2) * weightH p) *
            ‖cutRep c χ W p‖ₑ ^ (2 : ℝ) := by gcongr
      _ = ENNReal.ofReal ((1 + H1) ^ 2) *
            (weightH p * ‖cutRep c χ W p‖ₑ ^ (2 : ℝ)) := mul_assoc _ _ _

theorem lintegral_cutRep_sq_le {c σ H1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hs : ∀ p, χ p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1) {B : ℝ} (hB : ∀ p, |χ p| ≤ B) (hm : Measurable χ)
    (W : HSpace c MeridC) :
    ∫⁻ p, ‖cutRep c χ W p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * B * ‖W‖) ^ 2) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  let u := cutRep c χ W
  have hu : Measurable u := N05_4Aux.measurable_flatStressCutRep c hm W
  have hstep1 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((1 + H1) ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
    calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal ((1 + H1) ^ 2) *
            (weightH p * ‖u p‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
          lintegral_mono (cutRep_enorm_sq_le hσ hσH hs W)
      _ = ENNReal.ofReal ((1 + H1) ^ 2) *
            ∫⁻ p, weightH p * ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_const_mul _ ((measurable_weightH.mul (hu.enorm.pow_const (2 : ℝ))))
      _ = ENNReal.ofReal ((1 + H1) ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
          rw [measureH, lintegral_withDensity_eq_lintegral_mul _
            measurable_weightH (hu.enorm.pow_const (2 : ℝ))]
          rfl
  let U₀ := mulChi (measureH c) χ hm (hB) W
  have hae : (U₀ : Profile → MeridC) =ᵐ[measureH c] u :=
    N05_4Aux.flatStressCutRep_ae_eq hc χ hm (hB) W
  have hU0_norm : ‖U₀‖ ≤ B * ‖W‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_chi_smul (measureH c) χ hm
      (hB) (Lp.memLp W)).coeFn_toLp] with p hp
    change ‖((memLp_chi_smul (measureH c) χ hm
      (hB) (Lp.memLp W)).toLp _) p‖ ≤ _
    rw [hp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB p) (norm_nonneg _)
  have hstep2 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) ≤
      ENNReal.ofReal ((B * ‖W‖) ^ 2) := by
    have hcongr : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ∫⁻ p, ‖(U₀ : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with p hp
      rw [hp]
    have hLp : eLpNorm (U₀ : Profile → MeridC) 2 (measureH c) = ENNReal.ofReal ‖U₀‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top U₀)]
    have hlint : ∫⁻ p, ‖(U₀ : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ENNReal.ofReal (‖U₀‖ ^ 2) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := measureH c)
        (f := (U₀ : Profile → MeridC)) two_ne_zero ENNReal.ofNat_ne_top
      rw [hLp, ENNReal.toReal_ofNat] at heq
      have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq.symm
      rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg U₀) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two] at hpow
      exact hpow
    rw [hcongr, hlint]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg U₀) hU0_norm 2)
  calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ENNReal.ofReal ((1 + H1) ^ 2) * ENNReal.ofReal ((B * ‖W‖) ^ 2) := by
        refine hstep1.trans ?_
        gcongr
    _ = ENNReal.ofReal (((1 + H1) * B * ‖W‖) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- Unconditional `L²(cellMeasure c)` membership of `cutRep c χ W`. -/
theorem memLp_cutRep {c σ H1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hs : ∀ p, χ p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1) {B : ℝ} (hB : ∀ p, |χ p| ≤ B) (hm : Measurable χ)
    (W : HSpace c MeridC) :
    MemLp (cutRep c χ W) 2 (cellMeasure c) := by
  refine ⟨(N05_4Aux.measurable_flatStressCutRep c hm W).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  have hle := lintegral_cutRep_sq_le hc hσ hσH hs hB hm W
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne

/-- Unconditional unweighted `L²(cellMeasure c)` norm bound on `cutRep c χ W`. -/
theorem cellL2Norm_cutRep_le_mul {c σ H1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hs : ∀ p, χ p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1) {B : ℝ} (hB : ∀ p, |χ p| ≤ B) (hm : Measurable χ)
    (W : HSpace c MeridC) :
    cellL2Norm c (cutRep c χ W) ≤ (1 + H1) * B * ‖W‖ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  let u := cutRep c χ W
  have hmem := memLp_cutRep hc hσ hσH hs hB hm W
  have hint : Integrable (fun p => ‖u p‖ ^ 2) (cellMeasure c) :=
    hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hB0 : 0 ≤ (1 + H1) * B * ‖W‖ :=
    mul_nonneg (mul_nonneg (by linarith) hB0) (norm_nonneg W)
  have hint_le : ∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c) ≤ ((1 + H1) * B * ‖W‖) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [hofReal]
    exact lintegral_cutRep_sq_le hc hσ hσH hs hB hm W
  unfold cellL2Norm
  calc (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (((1 + H1) * B * ‖W‖) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = (1 + H1) * B * ‖W‖ := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hB0]

end N05_1_1P

end UnforcedLeray.Short.PartIIa
