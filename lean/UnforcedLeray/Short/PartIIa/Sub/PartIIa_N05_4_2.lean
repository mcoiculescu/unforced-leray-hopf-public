import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_4_1
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_2

/-!
# Audit Promotion for `PartII-a:N05/4/2`: age `s` 1/2-Hölder `L²(cellMeasure c)` bound for `χ S_0 F`

Source of record: `the November 2 reference manuscript`,
lines 1758–1764, 1785–1788 (`near:local-smoothing`, flat stress age regularity).

## Promoted infrastructure in this file

1. **Unconditional `L²_s H¹_{q,η}` bound on `u = flatStressCutRep c χ (T0flat hc ν μ G)`**
   (`flatCutL2H1Norm`, `flatCutL2H1Norm_le_gamma`):
   combines the unweighted `L²(cellMeasure c)` bound on `u` with the Leibniz spatial gradient bounds
   `cellL2Norm_flatCutSpatialDeriv_le_gamma` (`j = 0, 1`) from `Sub/PartII-a_N05_4_1.lean` to prove
   `flatCutL2H1Norm c χ (T0flat hc ν μ G) Gr ≤ 7 * Gamma^3 * ‖F‖`.
2. **Unconditional `L²_s H⁻¹_{q,η}` constituent bounds**
   (`flatDriftCutRep`, `lintegral_flatGradCutRep_fderiv_sq_le`,
   `cellL2Norm_flatGradCutRep_fderiv_le_mul`, `flatAgeDerivHminus1Norm`,
   `flatAgeDerivHminus1Norm_le_gamma`):
   bounds each zero-order and spatial divergence flux constituent on `cellMeasure c`, yielding
   `flatAgeDerivHminus1Norm ν c χ μ (T0flat hc ν μ G) Gr (tblkF c M) ≤ 18 * Gamma^5 * ‖F‖`.
3. **Unconditional large-shift bound (`min 1 (σ / 2) ≤ |h|`) and small-shift cutoff commutator bound
   (`|h| ≤ min 1 (σ / 2)`)**
   (`integral_shiftS_sub_sq_le_of_large`, `isNearCutoff_shiftCutoff`, `isNearCutoff_diffCutoff`,
   `abs_diffCutoff_le`, `integral_diffCutoff_smul_periodize_sq_le`,
   `integral_diffCutoff_smul_T0flat_sq_le_gamma`, `integral_shiftS_sub_sq_le_of_small`):
   - For large shifts `min 1 (σ / 2) ≤ |h|`, bounds the age-shift difference directly from the
     `L²(cellMeasure c)` norm of `u` and `1 ≤ (3 * Gamma) ^ 2 * |h|` without any PDE input.
   - For small shifts `|h| ≤ min 1 (σ / 2)`, splits
     `u (shiftS h p) - u p = χ (shiftS h p) • (b (shiftS h p) - b p) + (χ (shiftS h p) - χ p) • b p`
     and proves unconditionally via the mean-value theorem on `χ` that the cutoff commutator term is
     bounded by `(2 * Gamma^3 * ‖x‖)^2 * |h|`.
4. **Conditional assembly (`flatStressAgeHolderHalf_of`)**: reduces `FlatStressAgeHolderHalf` to the
   single band age-difference-quotient leaf `FlatBandAgeDiffQuotient` (`PartII-a:N05/4/2/1`) for the
   uncut solution `periodize c (T0flat hc ν μ G)` on the positive age band `|h| ≤ min 1 (σ / 2)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Axi
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.IIIa (tnorm2 tCalNorm IsCausalEnergySolution)
open UnforcedLeray.Short.PartIIIb.NearInst (cellPt)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (cpcHT_eq)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF tblkF)
open N05_4Aux N05_4_1Aux N05_2Aux

namespace N05_4_2Aux

/-! ### 1. Scalar multiplication and cutoff-derivative `flatGradCutRep` bounds on `cellMeasure c` -/

theorem cellL2Norm_const_smul_le (c : ℝ) (a : ℂ) (f : Profile → MeridC) :
    cellL2Norm c (fun p => a • f p) ≤ ‖a‖ * cellL2Norm c f := by
  unfold cellL2Norm
  have heq : (fun p : Profile => ‖a • f p‖ ^ 2) = fun p => ‖a‖ ^ 2 * ‖f p‖ ^ 2 := by
    funext p
    rw [norm_smul, mul_pow]
  rw [heq, integral_const_mul,
    Real.mul_rpow (sq_nonneg ‖a‖) (integral_nonneg fun _ => sq_nonneg _),
    ← Real.sqrt_eq_rpow (‖a‖ ^ 2), Real.sqrt_sq (norm_nonneg a)]

/-- Unweighted `L²(cellMeasure c)` bound on `flatGradCutRep c dχ Gr j` for any directional
derivative `dχ = fun q => fderiv ℝ χ q v` with `‖v‖ ≤ 1`, from `√c ‖Gr‖_𝒯 ≤ B_Gr`. -/
theorem lintegral_flatGradCutRep_fderiv_sq_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {v : Profile} (hv : ‖v‖ ≤ 1)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr) (j : Fin 2) :
    ∫⁻ p, ‖flatGradCutRep c (fun q => fderiv ℝ χ q v) Gr j p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ * B_Gr) ^ 2) := by
  let dχ : Profile → ℝ := fun q => fderiv ℝ χ q v
  have hdχ : IsNearCutoff c σ H1 L1 dχ := isNearCutoff_fderiv_apply hχ v
  have hmdχ : Measurable dχ := hdχ.smooth.continuous.measurable
  let g := flatGradCutRep c dχ Gr j
  have hg_meas : Measurable g := measurable_flatGradCutRep c hmdχ hGr j
  have htn_meas : Measurable (fun x => tnorm2 (Gr x)) := measurable_tnorm2 hGr
  have hcell_pt : ∀ᵐ p ∂(cellMeasure c),
      ‖g p‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
          (ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) := by
    filter_upwards [ae_cell_cellMeasure c] with p hpcell
    by_cases hp0 : g p = 0
    · simp [hp0]
    · obtain ⟨hs1, hs2, _⟩ := flatGradCutRep_support hdχ Gr j p hp0
      have hs_pos : 0 < p.1 := lt_of_lt_of_le hσ hs1
      have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
      have h1H1 : 1 ≤ 1 + H1 := by linarith
      have hp1H1 : p.1 ≤ 1 + H1 := by linarith
      have hrpow : p.1 ^ (1 / 2 : ℝ) ≤ (1 + H1) ^ 2 := by
        calc p.1 ^ (1 / 2 : ℝ)
            ≤ (1 + H1) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hs_pos.le hp1H1 (by norm_num)
          _ ≤ (1 + H1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1H1 (by norm_num)
          _ = (1 + H1) ^ 2 := Real.rpow_two (1 + H1)
      have h1 : 1 ≤ (1 + H1) ^ 2 * p.1 ^ (-(1 / 2 : ℝ)) := by
        calc (1 : ℝ)
            = p.1 ^ (1 / 2 : ℝ) * p.1 ^ (-(1 / 2 : ℝ)) := by
              rw [← Real.rpow_add hs_pos]; norm_num
          _ ≤ (1 + H1) ^ 2 * p.1 ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hs_pos.le _)
      have hgnorm : ‖g p‖ ≤ cNorm8 χ * ‖tnorm2 (Gr (cellPt c p))‖ := by
        dsimp only [g, flatGradCutRep]
        rw [periodize_of_mem hc _ hpcell, norm_smul, Real.norm_eq_abs,
          Real.norm_of_nonneg (by unfold tnorm2; exact Real.sqrt_nonneg _)]
        exact mul_le_mul (abs_fderiv_apply_le_cNorm8 hc hχ hv p)
          (norm_flatGradCol_le_tnorm2 c Gr j p) (norm_nonneg _) (cNorm8_nonneg χ)
      have hgsq : ‖g p‖ ^ 2 ≤ ((1 + H1) * cNorm8 χ) ^ 2 *
          (p.1 ^ (-(1 / 2 : ℝ)) * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) := by
        calc ‖g p‖ ^ 2
            ≤ (cNorm8 χ * ‖tnorm2 (Gr (cellPt c p))‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hgnorm 2
          _ = 1 * (cNorm8 χ ^ 2 * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) := by ring
          _ ≤ ((1 + H1) ^ 2 * p.1 ^ (-(1 / 2 : ℝ))) *
                (cNorm8 χ ^ 2 * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = ((1 + H1) * cNorm8 χ) ^ 2 *
                (p.1 ^ (-(1 / 2 : ℝ)) * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) := by ring
      have hLHS : ‖g p‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖g p‖ ^ 2) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          Real.rpow_two]
      have hRHS : ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            (ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) =
          ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2 *
            (p.1 ^ (-(1 / 2 : ℝ)) * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2)) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          Real.rpow_two, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs_pos.le _),
          ← ENNReal.ofReal_mul (sq_nonneg _)]
      rw [hLHS, hRHS]
      exact ENNReal.ofReal_le_ofReal hgsq
  have hstep1 : ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
        ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) := by
    have hm_tn : Measurable (fun p => ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) :=
      (htn_meas.comp (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPt c)).enorm.pow_const (2 : ℝ)
    have hm_w : Measurable (fun p : Profile => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ)))) :=
      ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
    calc ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            (ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) *
              ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
          lintegral_mono_ae hcell_pt
      _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) *
              ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_const_mul _ (hm_w.mul hm_tn)
      _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) := by
          rw [measureHT, lintegral_withDensity_eq_lintegral_mul _ hm_w hm_tn]
          rfl
  have hstep2 : ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) ≤
      ENNReal.ofReal (B_Gr ^ 2) := by
    have hmap : Measure.map (cellPt c) (measureHT c) = ENNReal.ofReal c • ageμ c (-1 / 2) :=
      cpcHT_eq c hc
    have hmap_lint : ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) =
        ENNReal.ofReal c * ∫⁻ x, ‖tnorm2 (Gr x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) := by
      rw [← lintegral_map (htn_meas.enorm.pow_const (2 : ℝ))
        (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPt c), hmap,
        lintegral_smul_measure, smul_eq_mul]
    have hCal_sq : ENNReal.ofReal c * ∫⁻ x, ‖tnorm2 (Gr x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) =
        (ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr) ^ (2 : ℝ) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := ageμ c (-1 / 2))
        (f := fun x => tnorm2 (Gr x)) two_ne_zero ENNReal.ofNat_ne_top
      rw [ENNReal.toReal_ofNat] at heq
      have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq
      rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one] at hpow
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg c) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two, Real.sq_sqrt hc.le, ← hpow]
      rfl
    rw [hmap_lint, hCal_sq]
    calc (ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr) ^ (2 : ℝ)
        ≤ (ENNReal.ofReal B_Gr) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hCal (by norm_num)
      _ = ENNReal.ofReal (B_Gr ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
  calc ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) * ENNReal.ofReal (B_Gr ^ 2) :=
        hstep1.trans (by gcongr)
    _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ * B_Gr) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        ring

theorem cellL2Norm_flatGradCutRep_fderiv_le_mul {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {v : Profile} (hv : ‖v‖ ≤ 1)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr) (j : Fin 2) :
    cellL2Norm c (flatGradCutRep c (fun q => fderiv ℝ χ q v) Gr j) ≤
      (1 + H1) * cNorm8 χ * B_Gr := by
  let dχ : Profile → ℝ := fun q => fderiv ℝ χ q v
  have hdχ : IsNearCutoff c σ H1 L1 dχ := isNearCutoff_fderiv_apply hχ v
  have hmdχ : Measurable dχ := hdχ.smooth.continuous.measurable
  let g := flatGradCutRep c dχ Gr j
  have hmem : MemLp g 2 (cellMeasure c) := by
    refine ⟨(measurable_flatGradCutRep c hmdχ hGr j).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat]
    have hle := lintegral_flatGradCutRep_fderiv_sq_le hc hσ hσH hχ hv hGr hB0 hCal j
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne
  have hint : Integrable (fun p => ‖g p‖ ^ 2) (cellMeasure c) :=
    hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖g p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hC0 : 0 ≤ (1 + H1) * cNorm8 χ * B_Gr :=
    mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) hB0
  have hint_le : ∫ p, ‖g p‖ ^ 2 ∂(cellMeasure c) ≤ ((1 + H1) * cNorm8 χ * B_Gr) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [hofReal]
    exact lintegral_flatGradCutRep_fderiv_sq_le hc hσ hσH hχ hv hGr hB0 hCal j
  unfold cellL2Norm
  calc (∫ p, ‖g p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (((1 + H1) * cNorm8 χ * B_Gr) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = (1 + H1) * cNorm8 χ * B_Gr := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hC0]

/-! ### 2. `L²_s H¹_{q,η}` and `L²_s H⁻¹_{q,η}` norms for `u` and `∂_s u` on `cellMeasure c` -/

/-- Concrete `L²_s H¹_{q,η}` norm of `u = flatStressCutRep c χ W` on `cellMeasure c`, combining the
`L²(cellMeasure c)` norm of `u` and its Leibniz `(q, η)` derivatives `flatCutSpatialDeriv c χ W Gr 0`
and `flatCutSpatialDeriv c χ W Gr 1`. -/
def flatCutL2H1Norm (c : ℝ) (χ : Profile → ℝ) (W : HSpace c MeridC)
    (Gr : Chart → Fin 2 → Fin 2 → ℂ) : ℝ :=
  cellL2Norm c (flatStressCutRep c χ W) +
    cellL2Norm c (flatCutSpatialDeriv c χ W Gr 0) +
    cellL2Norm c (flatCutSpatialDeriv c χ W Gr 1)

theorem flatCutL2H1Norm_nonneg (c : ℝ) (χ : Profile → ℝ) (W : HSpace c MeridC)
    (Gr : Chart → Fin 2 → Fin 2 → ℂ) :
    0 ≤ flatCutL2H1Norm c χ W Gr := by
  unfold flatCutL2H1Norm
  linarith [cellL2Norm_nonneg c (flatStressCutRep c χ W),
    cellL2Norm_nonneg c (flatCutSpatialDeriv c χ W Gr 0),
    cellL2Norm_nonneg c (flatCutSpatialDeriv c χ W Gr 1)]

/-- Unconditional `7 * Gamma^3 * ‖F‖` bound on `flatCutL2H1Norm c χ (T0flat hc ν μ G) Gr`. -/
theorem flatCutL2H1Norm_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) (F : HTSpace c) (G : HSpace c MeridC)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    (hH : ‖T0flat hc ν μ G‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤
      ENNReal.ofReal (ν⁻¹ * (Real.sqrt 2 * ‖F‖))) :
    flatCutL2H1Norm c χ (T0flat hc ν μ G) Gr ≤
      7 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖F‖ := by
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have hγi : 0 < γs⁻¹ := inv_pos.2 hγ
  have hG0 : 0 ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have h1H1_G : 1 + H1 ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hγ_G : γs⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hν_G : ν⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hsqrt_le : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ Gam := by
    have h1 : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ (Real.sqrt (γs * ν))⁻¹ := by
      refine inv_anti₀ (Real.sqrt_pos.2 (mul_pos hγ hν)) (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_right hμγ hν.le
    have h2 : ((Real.sqrt (γs * ν))⁻¹) ^ 2 ≤ Gam ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (mul_pos hγ hν).le, mul_inv, sq]
      exact mul_le_mul hγ_G hν_G hνi.le hG0
    exact h1.trans (abs_le_of_sq_le_sq' h2 hG0).2
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hu : cellL2Norm c (flatStressCutRep c χ (T0flat hc ν μ G)) ≤ Gam ^ 3 * ‖F‖ := by
    calc cellL2Norm c (flatStressCutRep c χ (T0flat hc ν μ G))
        ≤ (1 + H1) * cNorm8 χ * ‖T0flat hc ν μ G‖ :=
          cellL2Norm_flatStressCutRep_le_mul hc hσ hσH hχ hm (T0flat hc ν μ G)
      _ ≤ (1 + H1) * cNorm8 χ * ((Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖) :=
          mul_le_mul_of_nonneg_left hH (mul_nonneg (by linarith) (cNorm8_nonneg χ))
      _ = (1 + H1) * cNorm8 χ * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := by ring
      _ ≤ Gam * Gam * Gam * ‖F‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg F)
          refine mul_le_mul (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hsqrt_le
            (by positivity) (mul_nonneg hG0 hG0)
      _ = Gam ^ 3 * ‖F‖ := by ring
  have hd0 := cellL2Norm_flatCutSpatialDeriv_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hχ hm hμM hμγ
    F G hGr hH hCal 0
  have hd1 := cellL2Norm_flatCutSpatialDeriv_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hχ hm hμM hμγ
    F G hGr hH hCal 1
  unfold flatCutL2H1Norm
  linarith

/-- Concrete representative of the drift term `-(μ/s) χ b = (-μ) • dsFromS (flatStressCutRep c χ W)`
supported in `σ ≤ s ≤ H1`, `|η| ≤ L1`. -/
def flatDriftCutRep (c : ℝ) (χ : Profile → ℝ) (μ : ℂ) (W : HSpace c MeridC) (p : Profile) :
    MeridC :=
  (-μ) • dsFromS (flatStressCutRep c χ W) p

theorem cellL2Norm_flatDriftCutRep_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) (F : HTSpace c) (G : HSpace c MeridC)
    (hH : ‖T0flat hc ν μ G‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖) :
    cellL2Norm c (flatDriftCutRep c χ μ (T0flat hc ν μ G)) ≤
      Gamma ν c σ H1 L1 M γs χ χ1 ^ 5 * ‖F‖ := by
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have hγi : 0 < γs⁻¹ := inv_pos.2 hγ
  have hG0 : 0 ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hM_G : M ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have h1H1_G : 1 + H1 ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hγ_G : γs⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hν_G : ν⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hsqrt_le : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ Gam := by
    have h1 : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ (Real.sqrt (γs * ν))⁻¹ := by
      refine inv_anti₀ (Real.sqrt_pos.2 (mul_pos hγ hν)) (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_right hμγ hν.le
    have h2 : ((Real.sqrt (γs * ν))⁻¹) ^ 2 ≤ Gam ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (mul_pos hγ hν).le, mul_inv, sq]
      exact mul_le_mul hγ_G hν_G hνi.le hG0
    exact h1.trans (abs_le_of_sq_le_sq' h2 hG0).2
  let u := flatStressCutRep c χ (T0flat hc ν μ G)
  have hmem_u : MemLp u 2 (cellMeasure c) := memLp_flatStressCutRep hc hσ hσH hχ hm (T0flat hc ν μ G)
  have hsupp_u : ∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 :=
    flatStressCutRep_support hχ (T0flat hc ν μ G)
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hu_le : cellL2Norm c u ≤ Gam ^ 3 * ‖F‖ := by
    calc cellL2Norm c u
        ≤ (1 + H1) * cNorm8 χ * ‖T0flat hc ν μ G‖ :=
          cellL2Norm_flatStressCutRep_le_mul hc hσ hσH hχ hm (T0flat hc ν μ G)
      _ ≤ (1 + H1) * cNorm8 χ * ((Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖) :=
          mul_le_mul_of_nonneg_left hH (mul_nonneg (by linarith) (cNorm8_nonneg χ))
      _ = (1 + H1) * cNorm8 χ * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := by ring
      _ ≤ Gam * Gam * Gam * ‖F‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg F)
          refine mul_le_mul (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hsqrt_le
            (by positivity) (mul_nonneg hG0 hG0)
      _ = Gam ^ 3 * ‖F‖ := by ring
  have hds_le : cellL2Norm c (dsFromS u) ≤ Gam * (Gam ^ 3 * ‖F‖) := by
    calc cellL2Norm c (dsFromS u)
        ≤ Gam * cellL2Norm c u :=
          cellL2Norm_dsFromS_flat_le χ χ1 hν hc hσ hσH hL1 hγ hM0 hsupp_u hmem_u
      _ ≤ Gam * (Gam ^ 3 * ‖F‖) := mul_le_mul_of_nonneg_left hu_le hG0
  have hμ_Gam : ‖-μ‖ ≤ Gam := by
    rw [norm_neg]
    exact hμM.trans hM_G
  unfold flatDriftCutRep
  calc cellL2Norm c (fun p => (-μ) • dsFromS u p)
      ≤ ‖-μ‖ * cellL2Norm c (dsFromS u) := cellL2Norm_const_smul_le c (-μ) (dsFromS u)
    _ ≤ Gam * (Gam * (Gam ^ 3 * ‖F‖)) :=
        mul_le_mul hμ_Gam hds_le (cellL2Norm_nonneg c _) hG0
    _ = Gam ^ 5 * ‖F‖ := by ring

/-- Concrete `L²_s H⁻¹_{q,η}` norm of the weak age derivative
`∂_s u = (∂_s χ) b - (μ/s) χ b + ν χ Δ_{q,η} b + χ P_0 div_0 M` on `cellMeasure c`
(source lines 1758–1763), summing the `L²(cellMeasure c)` norms of the zero-order terms
`(∂_s χ) b`, `-(μ/s) χ b`, `-ν (∂_j χ) ∂_j b`, `(∂_j χ) M_{·j}` and the spatial divergence flux
terms `ν χ ∂_j b`, `χ M_{·j}` (`j = 0, 1`). -/
def flatAgeDerivHminus1Norm (ν c : ℝ) (χ : Profile → ℝ) (μ : ℂ) (W : HSpace c MeridC)
    (Gr Tblk : Chart → Fin 2 → Fin 2 → ℂ) : ℝ :=
  cellL2Norm c (flatStressCutRep c (pdS χ) W) +
    cellL2Norm c (flatDriftCutRep c χ μ W) +
    ∑ j : Fin 2,
      (cellL2Norm c (fun p => (ν : ℂ) • flatGradCutRep c (if j = 0 then pdQ χ else pdEta χ) Gr j p) +
        cellL2Norm c (flatGradCutRep c (if j = 0 then pdQ χ else pdEta χ) Tblk j) +
        cellL2Norm c (fun p => (ν : ℂ) • flatGradCutRep c χ Gr j p) +
        cellL2Norm c (flatGradCutRep c χ Tblk j))

theorem flatAgeDerivHminus1Norm_nonneg (ν c : ℝ) (χ : Profile → ℝ) (μ : ℂ) (W : HSpace c MeridC)
    (Gr Tblk : Chart → Fin 2 → Fin 2 → ℂ) :
    0 ≤ flatAgeDerivHminus1Norm ν c χ μ W Gr Tblk := by
  unfold flatAgeDerivHminus1Norm
  refine add_nonneg (add_nonneg (cellL2Norm_nonneg _ _) (cellL2Norm_nonneg _ _)) ?_
  refine Finset.sum_nonneg fun j _ => ?_
  linarith [cellL2Norm_nonneg c
      (fun p => (ν : ℂ) • flatGradCutRep c (if j = 0 then pdQ χ else pdEta χ) Gr j p),
    cellL2Norm_nonneg c (flatGradCutRep c (if j = 0 then pdQ χ else pdEta χ) Tblk j),
    cellL2Norm_nonneg c (fun p => (ν : ℂ) • flatGradCutRep c χ Gr j p),
    cellL2Norm_nonneg c (flatGradCutRep c χ Tblk j)]

/-- Unconditional `18 * Gamma^5 * ‖F‖` bound on
`flatAgeDerivHminus1Norm ν c χ μ (T0flat hc ν μ G) Gr (tblkF c M)` for any smooth tensor test `M`. -/
theorem flatAgeDerivHminus1Norm_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) {M_test : Profile → TensorVal} (hM_test : IsTensorTest c M_test)
    (F : HTSpace c) (G : HSpace c MeridC)
    (hF : (F : Profile → TensorVal) =ᵐ[measureHT c] M_test)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    (hH : ‖T0flat hc ν μ G‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤
      ENNReal.ofReal (ν⁻¹ * (Real.sqrt 2 * ‖F‖))) :
    flatAgeDerivHminus1Norm ν c χ μ (T0flat hc ν μ G) Gr (tblkF c M_test) ≤
      18 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 5 * ‖F‖ := by
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ Gam := gamma_ge_one χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have h1H1_G : 1 + H1 ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hγ_G : γs⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hν_G : ν⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hsqrt_le : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ Gam := by
    have h1 : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ (Real.sqrt (γs * ν))⁻¹ := by
      refine inv_anti₀ (Real.sqrt_pos.2 (mul_pos hγ hν)) (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_right hμγ hν.le
    have h2 : ((Real.sqrt (γs * ν))⁻¹) ^ 2 ≤ Gam ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (mul_pos hγ hν).le, mul_inv, sq]
      exact mul_le_mul hγ_G hν_G hνi.le hG0
    exact h1.trans (abs_le_of_sq_le_sq' h2 hG0).2
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hvS_norm : ‖((1 : ℝ), (0 : ℝ), (0 : ℝ))‖ ≤ 1 := by
    simp [Prod.norm_def]
  have hpdS_le : cellL2Norm c (flatStressCutRep c (pdS χ) (T0flat hc ν μ G)) ≤
      Gam ^ 5 * ‖F‖ := by
    have h35 : Gam ^ 3 ≤ Gam ^ 5 := pow_le_pow_right₀ hG1 (by omega)
    calc cellL2Norm c (flatStressCutRep c (pdS χ) (T0flat hc ν μ G))
        ≤ (1 + H1) * cNorm8 χ * ‖T0flat hc ν μ G‖ :=
          cellL2Norm_flatStressCutRep_fderiv_le_mul hc hσ hσH hχ hvS_norm (T0flat hc ν μ G)
      _ ≤ (1 + H1) * cNorm8 χ * ((Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖) :=
          mul_le_mul_of_nonneg_left hH (mul_nonneg (by linarith) (cNorm8_nonneg χ))
      _ = (1 + H1) * cNorm8 χ * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := by ring
      _ ≤ Gam * Gam * Gam * ‖F‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg F)
          refine mul_le_mul (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hsqrt_le
            (by positivity) (mul_nonneg hG0 hG0)
      _ = Gam ^ 3 * ‖F‖ := by ring
      _ ≤ Gam ^ 5 * ‖F‖ := mul_le_mul_of_nonneg_right h35 (norm_nonneg F)
  have hdrift_le : cellL2Norm c (flatDriftCutRep c χ μ (T0flat hc ν μ G)) ≤ Gam ^ 5 * ‖F‖ :=
    cellL2Norm_flatDriftCutRep_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hχ hm hμM hμγ F G hH
  have hTblk_meas : ∀ i j, Measurable (fun x => tblkF c M_test x i j) := fun i j =>
    UnforcedLeray.Short.PartIIIb.NearInst.Delta.fsf_measurable_tblkF
      hM_test.smooth.continuous.measurable i j
  have hTblk_cal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c (tblkF c M_test) ≤
      ENNReal.ofReal (Real.sqrt 2 * ‖F‖) :=
    N01.flatBlkTransport c hc M_test F hF
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    have hsq : (Real.sqrt 2) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    exact (abs_le_of_sq_le_sq' hsq (by norm_num)).2
  have h25 : Gam ^ 2 ≤ Gam ^ 5 := pow_le_pow_right₀ hG1 (by omega)
  have hGam2_le : (1 + H1) * cNorm8 χ * (Real.sqrt 2 * ‖F‖) ≤ 2 * Gam ^ 5 * ‖F‖ := by
    calc (1 + H1) * cNorm8 χ * (Real.sqrt 2 * ‖F‖)
        ≤ (1 + H1) * cNorm8 χ * (2 * ‖F‖) := by
          gcongr
          exact mul_nonneg (by linarith) (cNorm8_nonneg χ)
      _ = 2 * ((1 + H1) * cNorm8 χ) * ‖F‖ := by ring
      _ ≤ 2 * (Gam * Gam) * ‖F‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (norm_nonneg F)
          exact mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0
      _ = 2 * Gam ^ 2 * ‖F‖ := by ring
      _ ≤ 2 * Gam ^ 5 * ‖F‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h25 (by norm_num))
            (norm_nonneg F)
  have hj_le : ∀ j : Fin 2,
      cellL2Norm c (fun p => (ν : ℂ) • flatGradCutRep c (if j = 0 then pdQ χ else pdEta χ) Gr j p) +
        cellL2Norm c (flatGradCutRep c (if j = 0 then pdQ χ else pdEta χ) (tblkF c M_test) j) +
        cellL2Norm c (fun p => (ν : ℂ) • flatGradCutRep c χ Gr j p) +
        cellL2Norm c (flatGradCutRep c χ (tblkF c M_test) j) ≤
      8 * Gam ^ 5 * ‖F‖ := fun j => by
    let v : Profile := if j = 0 then (0, 1, 0) else (0, 0, 1)
    have hv_eq : (if j = 0 then pdQ χ else pdEta χ) = fun q => fderiv ℝ χ q v := by
      funext q
      by_cases hj : j = 0 <;> simp [hj, v, pdQ, pdEta]
    have hv_norm : ‖v‖ ≤ 1 := by
      by_cases hj : j = 0 <;> simp [hj, v, Prod.norm_def]
    have hB_Gr : 0 ≤ ν⁻¹ * (Real.sqrt 2 * ‖F‖) := by positivity
    have hB_Tblk : 0 ≤ Real.sqrt 2 * ‖F‖ := by positivity
    have hν_norm : ‖(ν : ℂ)‖ = ν := by
      rw [Complex.norm_real, Real.norm_of_nonneg hν.le]
    have ht1 : cellL2Norm c
        (fun p => (ν : ℂ) • flatGradCutRep c (if j = 0 then pdQ χ else pdEta χ) Gr j p) ≤
        2 * Gam ^ 5 * ‖F‖ := by
      rw [hv_eq]
      calc cellL2Norm c (fun p => (ν : ℂ) • flatGradCutRep c (fun q => fderiv ℝ χ q v) Gr j p)
          ≤ ‖(ν : ℂ)‖ * cellL2Norm c (flatGradCutRep c (fun q => fderiv ℝ χ q v) Gr j) :=
            cellL2Norm_const_smul_le c (ν : ℂ) _
        _ ≤ ν * ((1 + H1) * cNorm8 χ * (ν⁻¹ * (Real.sqrt 2 * ‖F‖))) := by
            rw [hν_norm]
            exact mul_le_mul_of_nonneg_left
              (cellL2Norm_flatGradCutRep_fderiv_le_mul hc hσ hσH hχ hv_norm hGr hB_Gr hCal j)
              hν.le
        _ = (1 + H1) * cNorm8 χ * (Real.sqrt 2 * ‖F‖) := by
            have hne : ν ≠ 0 := hν.ne'
            field_simp
        _ ≤ 2 * Gam ^ 5 * ‖F‖ := hGam2_le
    have ht2 : cellL2Norm c
        (flatGradCutRep c (if j = 0 then pdQ χ else pdEta χ) (tblkF c M_test) j) ≤
        2 * Gam ^ 5 * ‖F‖ := by
      rw [hv_eq]
      exact (cellL2Norm_flatGradCutRep_fderiv_le_mul hc hσ hσH hχ hv_norm hTblk_meas
        hB_Tblk hTblk_cal j).trans hGam2_le
    have ht3 : cellL2Norm c (fun p => (ν : ℂ) • flatGradCutRep c χ Gr j p) ≤
        2 * Gam ^ 5 * ‖F‖ := by
      calc cellL2Norm c (fun p => (ν : ℂ) • flatGradCutRep c χ Gr j p)
          ≤ ‖(ν : ℂ)‖ * cellL2Norm c (flatGradCutRep c χ Gr j) :=
            cellL2Norm_const_smul_le c (ν : ℂ) _
        _ ≤ ν * ((1 + H1) * cNorm8 χ * (ν⁻¹ * (Real.sqrt 2 * ‖F‖))) := by
            rw [hν_norm]
            exact mul_le_mul_of_nonneg_left
              (cellL2Norm_flatGradCutRep_le_mul hc hσ hσH hχ hm hGr hB_Gr hCal j) hν.le
        _ = (1 + H1) * cNorm8 χ * (Real.sqrt 2 * ‖F‖) := by
            have hne : ν ≠ 0 := hν.ne'
            field_simp
        _ ≤ 2 * Gam ^ 5 * ‖F‖ := hGam2_le
    have ht4 : cellL2Norm c (flatGradCutRep c χ (tblkF c M_test) j) ≤
        2 * Gam ^ 5 * ‖F‖ :=
      (cellL2Norm_flatGradCutRep_le_mul hc hσ hσH hχ hm hTblk_meas hB_Tblk hTblk_cal j).trans
        hGam2_le
    linarith
  unfold flatAgeDerivHminus1Norm
  rw [Fin.sum_univ_two]
  have hj0 := hj_le 0
  have hj1 := hj_le 1
  linarith

/-! ### 3. Unconditional large-shift bound and small-shift cutoff commutator bound -/

/-- General `L²(cellMeasure c)` lintegral bound for `flatStressCutRep c ψ W` with an explicit
supremum bound `∀ p, |ψ p| ≤ B`. -/
theorem lintegral_flatStressCutRep_sq_le_of_bound {c σ' H1' L1 : ℝ} (hc : 0 < c) (hσ' : 0 < σ')
    (hσH' : σ' ≤ H1') {ψ : Profile → ℝ} (hψ : IsNearCutoff c σ' H1' L1 ψ)
    {B : ℝ} (_hB0 : 0 ≤ B) (hB : ∀ p, |ψ p| ≤ B) (W : HSpace c MeridC) :
    ∫⁻ p, ‖flatStressCutRep c ψ W p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1') * B * ‖W‖) ^ 2) := by
  have hm : Measurable ψ := hψ.smooth.continuous.measurable
  let u := flatStressCutRep c ψ W
  have hu : Measurable u := measurable_flatStressCutRep c hm W
  have hstep1 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((1 + H1') ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
    calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal ((1 + H1') ^ 2) *
            (weightH p * ‖u p‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
          lintegral_mono (flatStressCutRep_enorm_sq_le hσ' hσH' hψ W)
      _ = ENNReal.ofReal ((1 + H1') ^ 2) *
            ∫⁻ p, weightH p * ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_const_mul _ (measurable_weightH.mul (hu.enorm.pow_const (2 : ℝ)))
      _ = ENNReal.ofReal ((1 + H1') ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
          rw [measureH, lintegral_withDensity_eq_lintegral_mul _
            measurable_weightH (hu.enorm.pow_const (2 : ℝ))]
          rfl
  let U₀ := mulChi (measureH c) ψ hm hB W
  have hae : (U₀ : Profile → MeridC) =ᵐ[measureH c] u :=
    flatStressCutRep_ae_eq hc ψ hm hB W
  have hU0_norm : ‖U₀‖ ≤ B * ‖W‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_chi_smul (measureH c) ψ hm hB (Lp.memLp W)).coeFn_toLp] with p hp
    change ‖((memLp_chi_smul (measureH c) ψ hm hB (Lp.memLp W)).toLp _) p‖ ≤ _
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
      ≤ ENNReal.ofReal ((1 + H1') ^ 2) * ENNReal.ofReal ((B * ‖W‖) ^ 2) :=
        hstep1.trans (by gcongr)
    _ = ENNReal.ofReal (((1 + H1') * B * ‖W‖) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

theorem integral_flatStressCutRep_sq_le_of_bound {c σ' H1' L1 : ℝ} (hc : 0 < c) (hσ' : 0 < σ')
    (hσH' : σ' ≤ H1') {ψ : Profile → ℝ} (hψ : IsNearCutoff c σ' H1' L1 ψ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ p, |ψ p| ≤ B) (W : HSpace c MeridC) :
    ∫ p, ‖flatStressCutRep c ψ W p‖ ^ 2 ∂(cellMeasure c) ≤
      ((1 + H1') * B * ‖W‖) ^ 2 := by
  have hm : Measurable ψ := hψ.smooth.continuous.measurable
  let u := flatStressCutRep c ψ W
  have hmem := memLp_flatStressCutRep hc hσ' hσH' hψ hm W
  have hint : Integrable (fun p => ‖u p‖ ^ 2) (cellMeasure c) :=
    hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
  rw [hofReal]
  exact lintegral_flatStressCutRep_sq_le_of_bound hc hσ' hσH' hψ hB0 hB W

/-- Shifted cutoff `(χ ∘ shiftS h) p = χ (shiftS h p)`. -/
def shiftCutoff (h : ℝ) (χ : Profile → ℝ) (p : Profile) : ℝ :=
  χ (shiftS h p)

/-- Cutoff age-shift difference `χ (shiftS h p) - χ p`. -/
def diffCutoff (h : ℝ) (χ : Profile → ℝ) (p : Profile) : ℝ :=
  χ (shiftS h p) - χ p

theorem contDiff_shiftS (h : ℝ) : ContDiff ℝ ∞ (shiftS h) :=
  (contDiff_fst.add contDiff_const).prodMk contDiff_snd

theorem isNearCutoff_shiftCutoff {c σ H1 L1 h : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (hh : |h| ≤ min 1 (σ / 2)) :
    IsNearCutoff c (σ / 2) (H1 + 1) L1 (shiftCutoff h χ) where
  smooth := hχ.smooth.comp (contDiff_shiftS h)
  periodic p := by
    rcases p with ⟨s, q, η⟩
    exact hχ.periodic (s + h, q, η)
  support p hp := by
    obtain ⟨hs1, hs2, hη⟩ := hχ.support (shiftS h p) hp
    change σ ≤ p.1 + h at hs1
    change p.1 + h ≤ H1 at hs2
    change |p.2.2| ≤ L1 at hη
    have hh1 : -1 ≤ h ∧ h ≤ 1 := abs_le.1 (hh.trans (min_le_left 1 (σ / 2)))
    have hh2 : -(σ / 2) ≤ h ∧ h ≤ σ / 2 := abs_le.1 (hh.trans (min_le_right 1 (σ / 2)))
    exact ⟨by linarith, by linarith, hη⟩

theorem isNearCutoff_diffCutoff {c σ H1 L1 h : ℝ} (hσ : 0 < σ) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (hh : |h| ≤ min 1 (σ / 2)) :
    IsNearCutoff c (σ / 2) (H1 + 1) L1 (diffCutoff h χ) where
  smooth := (hχ.smooth.comp (contDiff_shiftS h)).sub hχ.smooth
  periodic p := by
    rcases p with ⟨s, q, η⟩
    dsimp only [diffCutoff, shiftS]
    rw [hχ.periodic (s + h, q, η), hχ.periodic (s, q, η)]
  support p hp := by
    have hshift := isNearCutoff_shiftCutoff hχ hh
    by_cases h1 : shiftCutoff h χ p = 0
    · have h2 : χ p ≠ 0 := fun h0 => hp (by simp [diffCutoff, shiftCutoff] at h1 ⊢; linarith)
      obtain ⟨hs1, hs2, hη⟩ := hχ.support p h2
      exact ⟨by linarith, by linarith, hη⟩
    · exact hshift.support p h1

theorem abs_diffCutoff_le {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (h : ℝ) (p : Profile) :
    |diffCutoff h χ p| ≤ cNorm8 χ * |h| := by
  have hd : ∀ q ∈ (univ : Set Profile), DifferentiableAt ℝ χ q :=
    fun q _ => (hχ.smooth.differentiable (by decide)) q
  have hbd : ∀ q ∈ (univ : Set Profile), ‖fderiv ℝ χ q‖ ≤ cNorm8 χ :=
    fun q _ => norm_fderiv_le_cNorm8_of_nearCutoff hc hχ q
  have hmvt := convex_univ.norm_image_sub_le_of_norm_fderiv_le hd hbd (mem_univ p)
    (mem_univ (shiftS h p))
  have hnorm_sub : ‖shiftS h p - p‖ = |h| := by
    have heq : shiftS h p - p = (h, (0 : ℝ), (0 : ℝ)) := by
      rcases p with ⟨s, q, η⟩
      ext <;> simp [shiftS]
    rw [heq]
    simp [Prod.norm_def, Real.norm_eq_abs]
  rw [Real.norm_eq_abs, hnorm_sub] at hmvt
  exact hmvt

/-- Unconditional `L²(cellMeasure c)` bound on the cutoff age-shift commutator
`(χ (shiftS h p) - χ p) • periodize c W p` for `|h| ≤ min 1 (σ / 2)`. -/
theorem integral_diffCutoff_smul_periodize_sq_le {c σ H1 L1 h : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    (hh : |h| ≤ min 1 (σ / 2)) (W : HSpace c MeridC) :
    ∫ p, ‖(χ (shiftS h p) - χ p) • periodize c W p‖ ^ 2 ∂(cellMeasure c) ≤
      ((2 + H1) * cNorm8 χ * ‖W‖) ^ 2 * |h| := by
  have hσ2 : 0 < σ / 2 := half_pos hσ
  have hσH' : σ / 2 ≤ H1 + 1 := by linarith
  have hψ : IsNearCutoff c (σ / 2) (H1 + 1) L1 (diffCutoff h χ) :=
    isNearCutoff_diffCutoff hσ hχ hh
  have hB0 : 0 ≤ cNorm8 χ * |h| := mul_nonneg (cNorm8_nonneg χ) (abs_nonneg h)
  have hB : ∀ p, |diffCutoff h χ p| ≤ cNorm8 χ * |h| := abs_diffCutoff_le hc hχ h
  have hint := integral_flatStressCutRep_sq_le_of_bound hc hσ2 hσH' hψ hB0 hB W
  have hh1 : |h| ≤ 1 := hh.trans (min_le_left 1 (σ / 2))
  have hh_sq : |h| ^ 2 ≤ |h| := by
    calc |h| ^ 2 = |h| * |h| := sq |h|
      _ ≤ 1 * |h| := mul_le_mul_of_nonneg_right hh1 (abs_nonneg h)
      _ = |h| := one_mul |h|
  change ∫ p, ‖flatStressCutRep c (diffCutoff h χ) W p‖ ^ 2 ∂(cellMeasure c) ≤ _
  calc ∫ p, ‖flatStressCutRep c (diffCutoff h χ) W p‖ ^ 2 ∂(cellMeasure c)
      ≤ ((1 + (H1 + 1)) * (cNorm8 χ * |h|) * ‖W‖) ^ 2 := hint
    _ = ((2 + H1) * cNorm8 χ * ‖W‖) ^ 2 * |h| ^ 2 := by ring
    _ ≤ ((2 + H1) * cNorm8 χ * ‖W‖) ^ 2 * |h| :=
        mul_le_mul_of_nonneg_left hh_sq (sq_nonneg _)

/-- Unconditional `Gamma` bound on the cutoff age-shift commutator for `T0flat hc ν μ G` when
`|h| ≤ min 1 (σ / 2)`. -/
theorem integral_diffCutoff_smul_T0flat_sq_le_gamma {ν c σ H1 L1 M γs h : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M) (hμγ : γs ≤ μ.re + 1 / 4)
    (x : HTSpace c) (G : HSpace c MeridC)
    (hH : ‖T0flat hc ν μ G‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖x‖)
    (hh : |h| ≤ min 1 (σ / 2)) :
    ∫ p, ‖(χ (shiftS h p) - χ p) • periodize c (T0flat hc ν μ G) p‖ ^ 2 ∂(cellMeasure c) ≤
      (2 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖x‖) ^ 2 * |h| := by
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ Gam := gamma_ge_one χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have h2H1_G : 2 + H1 ≤ 2 * Gam := by
    have h1H1 : 1 + H1 ≤ Gam := by
      unfold Gam Gamma GammaBox
      have : 0 < c⁻¹ := inv_pos.2 hc
      have : 0 < σ⁻¹ := inv_pos.2 hσ
      have : 0 < γs⁻¹ := inv_pos.2 hγ
      linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
    linarith
  have hcN_G : cNorm8 χ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hγ_G : γs⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hν_G : ν⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hsqrt_le : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ Gam := by
    have h1 : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ (Real.sqrt (γs * ν))⁻¹ := by
      refine inv_anti₀ (Real.sqrt_pos.2 (mul_pos hγ hν)) (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_right hμγ hν.le
    have h2 : ((Real.sqrt (γs * ν))⁻¹) ^ 2 ≤ Gam ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (mul_pos hγ hν).le, mul_inv, sq]
      exact mul_le_mul hγ_G hν_G hνi.le hG0
    exact h1.trans (abs_le_of_sq_le_sq' h2 hG0).2
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hbase0 : 0 ≤ (2 + H1) * cNorm8 χ * ‖T0flat hc ν μ G‖ :=
    mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) (norm_nonneg _)
  have hbase : (2 + H1) * cNorm8 χ * ‖T0flat hc ν μ G‖ ≤ 2 * Gam ^ 3 * ‖x‖ := by
    calc (2 + H1) * cNorm8 χ * ‖T0flat hc ν μ G‖
        ≤ (2 + H1) * cNorm8 χ * ((Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖x‖) :=
          mul_le_mul_of_nonneg_left hH (mul_nonneg (by linarith) (cNorm8_nonneg χ))
      _ = (2 + H1) * cNorm8 χ * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖x‖ := by ring
      _ ≤ (2 * Gam) * Gam * Gam * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          refine mul_le_mul (mul_le_mul h2H1_G hcN_G (cNorm8_nonneg χ) (by positivity)) hsqrt_le
            (by positivity) (by positivity)
      _ = 2 * Gam ^ 3 * ‖x‖ := by ring
  calc ∫ p, ‖(χ (shiftS h p) - χ p) • periodize c (T0flat hc ν μ G) p‖ ^ 2 ∂(cellMeasure c)
      ≤ ((2 + H1) * cNorm8 χ * ‖T0flat hc ν μ G‖) ^ 2 * |h| :=
        integral_diffCutoff_smul_periodize_sq_le hc hσ hσH hχ hh (T0flat hc ν μ G)
    _ ≤ (2 * Gam ^ 3 * ‖x‖) ^ 2 * |h| :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hbase0 hbase 2) (abs_nonneg h)

/-- Small-shift splitting inequality (`|h| ≤ min 1 (σ / 2)`): decomposes
`flatStressCutRep c χ W (shiftS h p) - flatStressCutRep c χ W p` into the band age-shift
difference `χ (shiftS h p) • (periodize c W (shiftS h p) - periodize c W p)` and the cutoff
age-shift commutator `(χ (shiftS h p) - χ p) • periodize c W p`. -/
theorem integral_shiftS_sub_sq_le_of_small {c σ H1 L1 h : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    (hh : |h| ≤ min 1 (σ / 2)) (W : HSpace c MeridC) :
    ∫ p, ‖flatStressCutRep c χ W (shiftS h p) - flatStressCutRep c χ W p‖ ^ 2 ∂(cellMeasure c) ≤
      2 * ∫ p, ‖χ (shiftS h p) •
          (periodize c W (shiftS h p) - periodize c W p)‖ ^ 2 ∂(cellMeasure c) +
        2 * ∫ p, ‖(χ (shiftS h p) - χ p) • periodize c W p‖ ^ 2 ∂(cellMeasure c) := by
  have hσ2 : 0 < σ / 2 := half_pos hσ
  have hσH' : σ / 2 ≤ H1 + 1 := by linarith
  have hdiff_cut := isNearCutoff_diffCutoff hσ hχ hh
  have hm_diff : Measurable (diffCutoff h χ) := hdiff_cut.smooth.continuous.measurable
  let diff : Profile → MeridC := fun p =>
    flatStressCutRep c χ W (shiftS h p) - flatStressCutRep c χ W p
  let u1 : Profile → MeridC := fun p =>
    χ (shiftS h p) • (periodize c W (shiftS h p) - periodize c W p)
  let u2 : Profile → MeridC := fun p =>
    (χ (shiftS h p) - χ p) • periodize c W p
  have hmem_diff : MemLp diff 2 (cellMeasure c) := by
    have hm_d : Measurable diff :=
      ((measurable_flatStressCutRep c hm W).comp (measurable_shiftS h)).sub
        (measurable_flatStressCutRep c hm W)
    refine ⟨hm_d.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat]
    have hle := lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm (measurable_shiftS h)
      (fun f hf _ hsupp => lintegral_shiftS_le c h hf hsupp) W
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne
  have hmem2 : MemLp u2 2 (cellMeasure c) :=
    memLp_flatStressCutRep hc hσ2 hσH' hdiff_cut hm_diff W
  have hu1_eq : u1 = diff - u2 := by
    funext p
    simp only [u1, diff, u2, flatStressCutRep, Pi.sub_apply]
    rw [smul_sub, sub_smul, sub_sub_sub_cancel_right]
  have hmem1 : MemLp u1 2 (cellMeasure c) := by
    rw [hu1_eq]
    exact hmem_diff.sub hmem2
  have hint_diff : Integrable (fun p => ‖diff p‖ ^ 2) (cellMeasure c) :=
    hmem_diff.integrable_norm_pow two_ne_zero
  have hint1 : Integrable (fun p => ‖u1 p‖ ^ 2) (cellMeasure c) :=
    hmem1.integrable_norm_pow two_ne_zero
  have hint2 : Integrable (fun p => ‖u2 p‖ ^ 2) (cellMeasure c) :=
    hmem2.integrable_norm_pow two_ne_zero
  have hpt : ∀ p : Profile,
      ‖diff p‖ ^ 2 ≤ 2 * ‖u1 p‖ ^ 2 + 2 * ‖u2 p‖ ^ 2 := fun p => by
    have hsplit : diff p = u1 p + u2 p := by
      dsimp only [diff, flatStressCutRep, u1, u2]
      rw [smul_sub, sub_smul, sub_add_sub_cancel]
    have htri : ‖u1 p + u2 p‖ ≤ ‖u1 p‖ + ‖u2 p‖ := norm_add_le (u1 p) (u2 p)
    have hsq1 : ‖u1 p + u2 p‖ ^ 2 ≤ (‖u1 p‖ + ‖u2 p‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    rw [hsplit]
    nlinarith [sq_nonneg (‖u1 p‖ - ‖u2 p‖)]
  calc ∫ p, ‖diff p‖ ^ 2 ∂(cellMeasure c)
      ≤ ∫ p, (2 * ‖u1 p‖ ^ 2 + 2 * ‖u2 p‖ ^ 2) ∂(cellMeasure c) :=
        integral_mono hint_diff ((hint1.const_mul 2).add (hint2.const_mul 2)) hpt
    _ = 2 * ∫ p, ‖u1 p‖ ^ 2 ∂(cellMeasure c) + 2 * ∫ p, ‖u2 p‖ ^ 2 ∂(cellMeasure c) := by
        rw [integral_add (hint1.const_mul 2) (hint2.const_mul 2),
          integral_const_mul, integral_const_mul]

/-- Unconditional large-shift bound (`min 1 (σ / 2) ≤ |h|`): bounds the age-shift difference
directly from `lintegral_shift_sub_flatStressCutRep_sq_le` and `1 ≤ (3 * Gamma) ^ 2 * |h|` without
any PDE input. -/
theorem integral_shiftS_sub_sq_le_of_large {ν c σ H1 L1 M γs h : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) (x : HTSpace c) (G : HSpace c MeridC)
    (hH : ‖T0flat hc ν μ G‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖x‖)
    (hlarge : min 1 (σ / 2) ≤ |h|) :
    ∫ p, ‖flatStressCutRep c χ (T0flat hc ν μ G) (shiftS h p) -
        flatStressCutRep c χ (T0flat hc ν μ G) p‖ ^ 2 ∂(cellMeasure c) ≤
      (6 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 4 * ‖x‖) ^ 2 * |h| := by
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ Gam := gamma_ge_one χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have h1H1_G : 1 + H1 ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hσ_G : σ⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hγ_G : γs⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hν_G : ν⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hsqrt_le : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ Gam := by
    have h1 : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ (Real.sqrt (γs * ν))⁻¹ := by
      refine inv_anti₀ (Real.sqrt_pos.2 (mul_pos hγ hν)) (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_right hμγ hν.le
    have h2 : ((Real.sqrt (γs * ν))⁻¹) ^ 2 ≤ Gam ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (mul_pos hγ hν).le, mul_inv, sq]
      exact mul_le_mul hγ_G hν_G hνi.le hG0
    exact h1.trans (abs_le_of_sq_le_sq' h2 hG0).2
  let W := T0flat hc ν μ G
  let diff := fun p => flatStressCutRep c χ W (shiftS h p) - flatStressCutRep c χ W p
  have hmem : MemLp diff 2 (cellMeasure c) := by
    have hm_d : Measurable diff :=
      ((measurable_flatStressCutRep c hm W).comp (measurable_shiftS h)).sub
        (measurable_flatStressCutRep c hm W)
    refine ⟨hm_d.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat]
    have hle := lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm (measurable_shiftS h)
      (fun f hf _ hsupp => lintegral_shiftS_le c h hf hsupp) W
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne
  have hint : Integrable (fun p => ‖diff p‖ ^ 2) (cellMeasure c) :=
    hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖diff p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖diff p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hint_le : ∫ p, ‖diff p‖ ^ 2 ∂(cellMeasure c) ≤ (2 * ((1 + H1) * cNorm8 χ * ‖W‖)) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [hofReal]
    exact lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm (measurable_shiftS h)
      (fun f hf _ hsupp => lintegral_shiftS_le c h hf hsupp) W
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have h2W_0 : 0 ≤ 2 * ((1 + H1) * cNorm8 χ * ‖W‖) :=
    mul_nonneg zero_le_two (mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) (norm_nonneg W))
  have h2W_le : 2 * ((1 + H1) * cNorm8 χ * ‖W‖) ≤ 2 * Gam ^ 3 * ‖x‖ := by
    calc 2 * ((1 + H1) * cNorm8 χ * ‖W‖)
        ≤ 2 * ((1 + H1) * cNorm8 χ * ((Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖x‖)) := by
          gcongr
          exact mul_nonneg (by linarith) (cNorm8_nonneg χ)
      _ = 2 * ((1 + H1) * cNorm8 χ * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹) * ‖x‖ := by ring
      _ ≤ 2 * (Gam * Gam * Gam) * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (norm_nonneg x)
          refine mul_le_mul (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hsqrt_le
            (by positivity) (mul_nonneg hG0 hG0)
      _ = 2 * Gam ^ 3 * ‖x‖ := by ring
  have h1_le_h : 1 ≤ (3 * Gam) ^ 2 * |h| := by
    have hmin_le : 1 ≤ 3 * Gam * min 1 (σ / 2) := by
      rcases le_total 1 (σ / 2) with hle | hle
      · rw [min_eq_left hle]
        linarith
      · rw [min_eq_right hle]
        have hσ_inv : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ.ne'
        have h2G : 2 * σ⁻¹ ≤ 3 * Gam := by linarith [inv_pos.2 hσ]
        calc (1 : ℝ) = (2 * σ⁻¹) * (σ / 2) := by linarith [hσ_inv]
          _ ≤ (3 * Gam) * (σ / 2) := mul_le_mul_of_nonneg_right h2G (by positivity)
    calc (1 : ℝ) ≤ 3 * Gam * min 1 (σ / 2) := hmin_le
      _ ≤ 3 * Gam * |h| := mul_le_mul_of_nonneg_left hlarge (by positivity)
      _ ≤ (3 * Gam) * (3 * Gam) * |h| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg h)
          nlinarith
      _ = (3 * Gam) ^ 2 * |h| := by ring
  calc ∫ p, ‖diff p‖ ^ 2 ∂(cellMeasure c)
      ≤ (2 * ((1 + H1) * cNorm8 χ * ‖W‖)) ^ 2 := hint_le
    _ ≤ (2 * Gam ^ 3 * ‖x‖) ^ 2 * 1 := by
        rw [mul_one]
        exact pow_le_pow_left₀ h2W_0 h2W_le 2
    _ ≤ (2 * Gam ^ 3 * ‖x‖) ^ 2 * ((3 * Gam) ^ 2 * |h|) :=
        mul_le_mul_of_nonneg_left h1_le_h (sq_nonneg _)
    _ = (6 * Gam ^ 4 * ‖x‖) ^ 2 * |h| := by ring

end N05_4_2Aux

open N05_4_2Aux

/-! ### 4. Band age difference-quotient leaf and conditional assembly of `FlatStressAgeHolderHalf` -/

/-- **Band age difference-quotient leaf for `PartII-a:N05/4/2` (`PartII-a:N05/4/2/1`)**
(source `the November 2 reference manuscript`,
lines 1758–1764, 1785–1788): for any smooth tensor test `M_test` (`IsTensorTest c M_test`) and its
causal energy solution `(b, Gr)` of the flat equation `(∂_s + μ/s - νΔ_{q,η}) b = P_0 div_0 M_test`
(`IsCausalEnergySolution c ν μ 0 (tblkF c M_test) b Gr`) satisfying the energy, gradient, and
forcing bounds, and any small age shift `|h| ≤ min 1 (σ / 2)` (so that on `χ (shiftS h p) ≠ 0` both
`p.1 + h ∈ [σ, H1]` and `p.1 ∈ [σ / 2, H1 + 1 / 2]` lie inside the positive age band away from
`s = 0`), multiplying `b` by a 1D age-only cutoff on `[σ / 4, H1 + 2]` and applying `(H⁻¹, H¹)`
duality / 1D Fourier Cauchy-Schwarz bounds the weighted age difference quotient
`∫ p, ‖χ (shiftS h p) • (periodize c (T0flat hc ν μ G) (shiftS h p) - periodize c (T0flat hc ν μ G) p)‖ ^ 2 ∂(cellMeasure c)`
by `(C * Gamma^k * ‖x‖)^2 * |h|`. -/
def FlatBandAgeDiffQuotient : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ),
      0 < ν → ∀ (hc : 0 < c), 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → Measurable χ →
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ (M_test : Profile → TensorVal), IsTensorTest c M_test →
          ∀ (x : HTSpace c) (G : HSpace c MeridC),
            (x : Profile → TensorVal) =ᵐ[measureHT c] M_test →
            (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M_test p) →
            ∀ (b : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
              b =ᵐ[ageμ c (-3 / 2)] velF c (T0flat hc ν μ G) →
              IsCausalEnergySolution c ν μ (fun _ _ _ => 0) (tblkF c M_test) b Gr →
              ‖T0flat hc ν μ G‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖x‖ →
              ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤
                ENNReal.ofReal (ν⁻¹ * (Real.sqrt 2 * ‖x‖)) →
              ENNReal.ofReal (Real.sqrt c) * tCalNorm c (tblkF c M_test) ≤
                ENNReal.ofReal (Real.sqrt 2 * ‖x‖) →
              ∀ h : ℝ, |h| ≤ min 1 (σ / 2) →
                ∫ p, ‖χ (shiftS h p) •
                    (periodize c (T0flat hc ν μ G) (shiftS h p) -
                      periodize c (T0flat hc ν μ G) p)‖ ^ 2 ∂(cellMeasure c) ≤
                  (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖x‖) ^ 2 * |h|

/-- **Conditional assembly of `FlatStressAgeHolderHalf` (`PartII-a:N05/4/2`)** from
`FlatBandAgeDiffQuotient`, using the unconditional `N05_4Aux.flatSmoothEnergyAndGrad` theorem,
`N01.flatBlkTransport`, the unconditional large-shift bound `integral_shiftS_sub_sq_le_of_large`,
the unconditional small-shift splitting `integral_shiftS_sub_sq_le_of_small`, the unconditional
cutoff age-shift commutator bound `integral_diffCutoff_smul_T0flat_sq_le_gamma`, `lintegral_shiftS_le`,
and the unconditional density extension `integral_shift_sub_sq_le_of_testSub` from `N01.testSub c`
to `HTSpace c`. -/
theorem flatStressAgeHolderHalf_of (hBand : FlatBandAgeDiffQuotient) :
    FlatStressAgeHolderHalf := by
  obtain ⟨k, C, hC0, hB⟩ := hBand
  set K := max k 4
  refine ⟨K, 4 * (C + 6), by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ _hχ1 hm _B _hB μ hμM hμγ S0 hS0 F h _hh
  have hμ_pos : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγ hμγ
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ Gam := gamma_ge_one χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hGK_k : Gam ^ k ≤ Gam ^ K := pow_le_pow_right₀ hG1 (le_max_left k 4)
  have hGK_4 : Gam ^ 4 ≤ Gam ^ K := pow_le_pow_right₀ hG1 (le_max_right k 4)
  have hGK_3 : Gam ^ 3 ≤ Gam ^ K :=
    (pow_le_pow_right₀ hG1 (by omega : 3 ≤ 4)).trans hGK_4
  have hK0 : 0 ≤ (2 * (C + 6) * Gam ^ K) ^ 2 * |h| :=
    mul_nonneg (sq_nonneg _) (abs_nonneg h)
  have hext := integral_shift_sub_sq_le_of_testSub hc hν hσ hσH hχ hm hμ_pos hS0
    (measurable_shiftS h)
    (fun f hf _ hsupp => lintegral_shiftS_le c h hf hsupp)
    hK0
    (fun M' hM' x G hxM' hG => by
      obtain ⟨b, Gr, hbv, hsol, hH, hCal⟩ :=
        flatSmoothEnergyAndGrad hc hν hμ_pos hM' x G hxM' hG
      have hTblk_cal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c (tblkF c M') ≤
          ENNReal.ofReal (Real.sqrt 2 * ‖x‖) :=
        N01.flatBlkTransport c hc M' x hxM'
      rcases le_total |h| (min 1 (σ / 2)) with hsmall | hlarge
      · have hsplit := integral_shiftS_sub_sq_le_of_small hc hσ hσH hχ hm hsmall (T0flat hc ν μ G)
        have hband := hB ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hm μ hμM hμγ
          M' hM' x G hxM' hG b Gr hbv hsol hH hCal hTblk_cal h hsmall
        have hcomm := integral_diffCutoff_smul_T0flat_sq_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hχ
          hμM hμγ x G hH hsmall
        have hband' : (C * Gam ^ k * ‖x‖) ^ 2 ≤ (C * Gam ^ K * ‖x‖) ^ 2 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGK_k hC0) (norm_nonneg x)
        have hcomm' : (2 * Gam ^ 3 * ‖x‖) ^ 2 ≤ (2 * Gam ^ K * ‖x‖) ^ 2 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hGK_3 (by norm_num)) (norm_nonneg x)
        have hsum_sq :
            2 * ((C * Gam ^ K * ‖x‖) ^ 2 * |h|) + 2 * ((2 * Gam ^ K * ‖x‖) ^ 2 * |h|) ≤
              ((2 * (C + 6) * Gam ^ K) ^ 2 * |h|) * ‖x‖ ^ 2 := by
          have h1 : 2 * C ^ 2 + 2 * 2 ^ 2 ≤ (2 * (C + 6)) ^ 2 := by nlinarith
          calc 2 * ((C * Gam ^ K * ‖x‖) ^ 2 * |h|) + 2 * ((2 * Gam ^ K * ‖x‖) ^ 2 * |h|)
              = (2 * C ^ 2 + 2 * 2 ^ 2) * ((Gam ^ K) ^ 2 * |h| * ‖x‖ ^ 2) := by ring
            _ ≤ (2 * (C + 6)) ^ 2 * ((Gam ^ K) ^ 2 * |h| * ‖x‖ ^ 2) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = ((2 * (C + 6) * Gam ^ K) ^ 2 * |h|) * ‖x‖ ^ 2 := by ring
        calc ∫ p, ‖flatStressCutRep c χ (T0flat hc ν μ G) (shiftS h p) -
                flatStressCutRep c χ (T0flat hc ν μ G) p‖ ^ 2 ∂(cellMeasure c)
            ≤ 2 * ((C * Gam ^ k * ‖x‖) ^ 2 * |h|) + 2 * ((2 * Gam ^ 3 * ‖x‖) ^ 2 * |h|) :=
              hsplit.trans (add_le_add (mul_le_mul_of_nonneg_left hband (by norm_num))
                (mul_le_mul_of_nonneg_left hcomm (by norm_num)))
          _ ≤ 2 * ((C * Gam ^ K * ‖x‖) ^ 2 * |h|) + 2 * ((2 * Gam ^ K * ‖x‖) ^ 2 * |h|) :=
              add_le_add
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hband' (abs_nonneg h)) (by norm_num))
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hcomm' (abs_nonneg h)) (by norm_num))
          _ ≤ ((2 * (C + 6) * Gam ^ K) ^ 2 * |h|) * ‖x‖ ^ 2 := hsum_sq
      · have hlg := integral_shiftS_sub_sq_le_of_large χ χ1 hν hc hσ hσH hL1 hγ hχ hm hμM hμγ
          x G hH hlarge
        have hlg' : (6 * Gam ^ 4 * ‖x‖) ^ 2 ≤ (2 * (C + 6) * Gam ^ K * ‖x‖) ^ 2 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          refine mul_le_mul (by linarith) hGK_4 (pow_nonneg hG0 4) (by positivity)
        calc ∫ p, ‖flatStressCutRep c χ (T0flat hc ν μ G) (shiftS h p) -
                flatStressCutRep c χ (T0flat hc ν μ G) p‖ ^ 2 ∂(cellMeasure c)
            ≤ (6 * Gam ^ 4 * ‖x‖) ^ 2 * |h| := hlg
          _ ≤ (2 * (C + 6) * Gam ^ K * ‖x‖) ^ 2 * |h| :=
              mul_le_mul_of_nonneg_right hlg' (abs_nonneg h)
          _ = ((2 * (C + 6) * Gam ^ K) ^ 2 * |h|) * ‖x‖ ^ 2 := by ring)
    F
  calc ∫ p, ‖flatStressCutRep c χ (S0 F) (shiftS h p) -
          flatStressCutRep c χ (S0 F) p‖ ^ 2 ∂(cellMeasure c)
      ≤ 2 * (((2 * (C + 6) * Gam ^ K) ^ 2 * |h|) * ‖F‖ ^ 2) := hext
    _ ≤ (4 * (C + 6) * Gam ^ K * ‖F‖) ^ 2 * |h| := by
        have : 0 ≤ (C + 6) ^ 2 * (Gam ^ K) ^ 2 * ‖F‖ ^ 2 * |h| := by positivity
        nlinarith

end UnforcedLeray.Short.PartIIa
