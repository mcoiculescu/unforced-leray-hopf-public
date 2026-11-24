import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_4_2
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.AgeHolderHalf.MollifiedSteklov
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree.FreeEnergyFlatSq

/-!
# Proof of `FlatBandAgeDiffQuotient` (`PartII-a:N05/4/2`)

Source of record: `the November 2 reference manuscript`,
lines 1758–1764, 1785–1788 (`near:local-smoothing`, flat stress age regularity).

Combines the positive-age band Steklov difference bound `N05_4_2Steklov.lintegral_band_diff_le`
with `N01.flatVelTransport`, `IIIa.normSq`, `IIIa.ageSlice`, `IIIa.sliceLoc`, `IIIa.gainLocF`,
`N01.cellPtInv_map`, and `lintegral_shiftS_le` to prove `FlatBandAgeDiffQuotient` unconditionally.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (volCyl_ac_ageμ)
open UnforcedLeray.Short.IIIa
  (vnorm2 tnorm2 hCalNorm tCalNorm energyE energyN sliceSq FreeSolData IsCausalEnergySolution)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (cellPtInv measurable_cellPtInv)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta
  (velF tblkF fsf_vnorm2_eq_norm fsf_measurable_tblkF fsf_gainConj_zero)
open N05_4Aux N05_4_1Aux N05_4_2Aux N05_4_2Steklov

namespace N05_4_2BandAux

/-- Unweighted band integral bound on `energyE c b` over `Icc (σ / 2) (H1 + 1)` from
`b =ᵐ[ageμ c (-3 / 2)] velF c W` via `N01.flatVelTransport`, `IIIa.normSq`, and `IIIa.ageSlice`. -/
theorem integral_energyE_band_le {c σ H1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {W : HSpace c MeridC} {b : Chart → Fin 2 → ℂ}
    (hbv : b =ᵐ[ageμ c (-3 / 2)] velF c W)
    (hbm : ∀ i, Measurable fun p => b p i)
    (hb_loc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2) < ⊤) :
    ∫ s in Icc (σ / 2) (H1 + 1), energyE c b s ≤ ((2 + H1) * ‖W‖) ^ 2 := by
  set gV : Chart → ℝ := fun p => vnorm2 (b p) ^ 2
  have hgVm : Measurable gV := UnforcedLeray.Short.IIIa.measurable_vnorm2_sq hbm
  have hgV0 : ∀ p, 0 ≤ gV p := fun _ => sq_nonneg _
  have hIntE : IntegrableOn (energyE c b) (Icc (σ / 2) (H1 + 1)) :=
    (UnforcedLeray.Short.IIIa.sliceLoc c gV hc hgVm hgV0 hb_loc).2.1
      (σ / 2) (H1 + 1) (half_pos hσ) (by linarith)
  have hV := N01.flatVelTransport c hc W b hbv
  have hV_sq : ENNReal.ofReal (‖W‖ ^ 2) = ENNReal.ofReal c * hCalNorm c b ^ 2 := by
    calc ENNReal.ofReal (‖W‖ ^ 2)
        = (ENNReal.ofReal ‖W‖) ^ 2 := ENNReal.ofReal_pow (norm_nonneg W) 2
      _ = (ENNReal.ofReal (Real.sqrt c) * hCalNorm c b) ^ 2 := by rw [hV]
      _ = (ENNReal.ofReal (Real.sqrt c)) ^ 2 * hCalNorm c b ^ 2 := mul_pow _ _ 2
      _ = ENNReal.ofReal c * hCalNorm c b ^ 2 := by
          rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg c) 2, Real.sq_sqrt hc.le]
  have hAge : hCalNorm c b ^ 2 = ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * energyE c b s) := by
    rw [UnforcedLeray.Short.IIIa.normSq.1]
    exact (UnforcedLeray.Short.IIIa.ageSlice c (-3 / 2) gV hc hgVm hgV0 hb_loc).1
  have hWeighted : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * energyE c b s) =
      ENNReal.ofReal (‖W‖ ^ 2) := by
    rw [hV_sq, hAge, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
      ENNReal.ofReal_one, one_mul]
  have hpt : ∀ s ∈ Icc (σ / 2) (H1 + 1),
      ENNReal.ofReal (energyE c b s) ≤
        ENNReal.ofReal ((2 + H1) ^ 2) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * energyE c b s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (half_pos hσ) hs.1
    have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
    have h2H1_1 : 1 ≤ 2 + H1 := by linarith
    have hs_le : s ≤ 2 + H1 := by linarith [hs.2]
    have hrpow : s ^ (3 / 2 : ℝ) ≤ (2 + H1) ^ 2 := by
      calc s ^ (3 / 2 : ℝ)
          ≤ (2 + H1) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hs0.le hs_le (by norm_num)
        _ ≤ (2 + H1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2H1_1 (by norm_num)
        _ = (2 + H1) ^ 2 := Real.rpow_two (2 + H1)
    have h1 : 1 ≤ (2 + H1) ^ 2 * s ^ (-3 / 2 : ℝ) := by
      calc (1 : ℝ) = s ^ (3 / 2 : ℝ) * s ^ (-3 / 2 : ℝ) := by
            rw [← Real.rpow_add hs0]; norm_num
        _ ≤ (2 + H1) ^ 2 * s ^ (-3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hs0.le _)
    have hE0 : 0 ≤ energyE c b s := integral_nonneg fun _ => sq_nonneg _
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc energyE c b s = 1 * energyE c b s := (one_mul _).symm
      _ ≤ ((2 + H1) ^ 2 * s ^ (-3 / 2 : ℝ)) * energyE c b s :=
          mul_le_mul_of_nonneg_right h1 hE0
      _ = (2 + H1) ^ 2 * (s ^ (-3 / 2 : ℝ) * energyE c b s) := by ring
  refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
  rw [ofReal_integral_eq_lintegral_ofReal hIntE
    (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)]
  calc ∫⁻ s in Icc (σ / 2) (H1 + 1), ENNReal.ofReal (energyE c b s)
      ≤ ∫⁻ s in Icc (σ / 2) (H1 + 1),
          ENNReal.ofReal ((2 + H1) ^ 2) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * energyE c b s) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal ((2 + H1) ^ 2) *
          ∫⁻ s in Icc (σ / 2) (H1 + 1), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * energyE c b s) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2 + H1) ^ 2) *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * energyE c b s) := by
        gcongr
        exact fun s hs => lt_of_lt_of_le (half_pos hσ) hs.1
    _ = ENNReal.ofReal (((2 + H1) * ‖W‖) ^ 2) := by
        rw [hWeighted, ← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        ring

/-- Unweighted band integral bound on `energyN c T` over `Icc (σ / 2) (H1 + 1)` from
`√c ‖T‖_𝒯 ≤ B` via `IIIa.normSq` and `IIIa.ageSlice`. -/
theorem integral_energyN_band_le {c σ H1 B : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    (hB0 : 0 ≤ B) {T : Chart → Fin 2 → Fin 2 → ℂ}
    (hTm : ∀ i j, Measurable fun p => T p i j)
    (hT_loc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (T p) ^ 2) < ⊤)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c T ≤ ENNReal.ofReal B) :
    ∫ s in Icc (σ / 2) (H1 + 1), energyN c T s ≤ ((2 + H1) * B) ^ 2 := by
  set gT : Chart → ℝ := fun p => tnorm2 (T p) ^ 2
  have hgTm : Measurable gT := (UnforcedLeray.Short.IIIa.measurable_tnorm2 hTm).pow_const 2
  have hgT0 : ∀ p, 0 ≤ gT p := fun _ => sq_nonneg _
  have hIntN : IntegrableOn (energyN c T) (Icc (σ / 2) (H1 + 1)) :=
    (UnforcedLeray.Short.IIIa.sliceLoc c gT hc hgTm hgT0 hT_loc).2.1
      (σ / 2) (H1 + 1) (half_pos hσ) (by linarith)
  have hCal_sq : ENNReal.ofReal c * tCalNorm c T ^ 2 ≤ ENNReal.ofReal (B ^ 2) := by
    calc ENNReal.ofReal c * tCalNorm c T ^ 2
        = (ENNReal.ofReal (Real.sqrt c)) ^ 2 * tCalNorm c T ^ 2 := by
          rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg c) 2, Real.sq_sqrt hc.le]
      _ = (ENNReal.ofReal (Real.sqrt c) * tCalNorm c T) ^ 2 := (mul_pow _ _ 2).symm
      _ ≤ (ENNReal.ofReal B) ^ 2 := pow_le_pow_left₀ zero_le hCal 2
      _ = ENNReal.ofReal (B ^ 2) := (ENNReal.ofReal_pow hB0 2).symm
  have hAge : tCalNorm c T ^ 2 = ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * energyN c T s) := by
    rw [UnforcedLeray.Short.IIIa.normSq.2]
    exact (UnforcedLeray.Short.IIIa.ageSlice c (-1 / 2) gT hc hgTm hgT0 hT_loc).1
  have hWeighted : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * energyN c T s) ≤
      ENNReal.ofReal (B ^ 2) := by
    have h1 : ENNReal.ofReal c * tCalNorm c T ^ 2 =
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * energyN c T s) := by
      rw [hAge, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
        ENNReal.ofReal_one, one_mul]
    rwa [← h1]
  have hpt : ∀ s ∈ Icc (σ / 2) (H1 + 1),
      ENNReal.ofReal (energyN c T s) ≤
        ENNReal.ofReal ((2 + H1) ^ 2) * ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * energyN c T s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (half_pos hσ) hs.1
    have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
    have h2H1_1 : 1 ≤ 2 + H1 := by linarith
    have hs_le : s ≤ 2 + H1 := by linarith [hs.2]
    have hrpow : s ^ (1 / 2 : ℝ) ≤ (2 + H1) ^ 2 := by
      calc s ^ (1 / 2 : ℝ)
          ≤ (2 + H1) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hs0.le hs_le (by norm_num)
        _ ≤ (2 + H1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2H1_1 (by norm_num)
        _ = (2 + H1) ^ 2 := Real.rpow_two (2 + H1)
    have h1 : 1 ≤ (2 + H1) ^ 2 * s ^ (-1 / 2 : ℝ) := by
      calc (1 : ℝ) = s ^ (1 / 2 : ℝ) * s ^ (-1 / 2 : ℝ) := by
            rw [← Real.rpow_add hs0]; norm_num
        _ ≤ (2 + H1) ^ 2 * s ^ (-1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hs0.le _)
    have hN0 : 0 ≤ energyN c T s := integral_nonneg fun _ => sq_nonneg _
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc energyN c T s = 1 * energyN c T s := (one_mul _).symm
      _ ≤ ((2 + H1) ^ 2 * s ^ (-1 / 2 : ℝ)) * energyN c T s :=
          mul_le_mul_of_nonneg_right h1 hN0
      _ = (2 + H1) ^ 2 * (s ^ (-1 / 2 : ℝ) * energyN c T s) := by ring
  refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
  rw [ofReal_integral_eq_lintegral_ofReal hIntN
    (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)]
  calc ∫⁻ s in Icc (σ / 2) (H1 + 1), ENNReal.ofReal (energyN c T s)
      ≤ ∫⁻ s in Icc (σ / 2) (H1 + 1),
          ENNReal.ofReal ((2 + H1) ^ 2) * ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * energyN c T s) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal ((2 + H1) ^ 2) *
          ∫⁻ s in Icc (σ / 2) (H1 + 1), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * energyN c T s) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2 + H1) ^ 2) *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * energyN c T s) := by
        gcongr
        exact fun s hs => lt_of_lt_of_le (half_pos hσ) hs.1
    _ ≤ ENNReal.ofReal ((2 + H1) ^ 2) * ENNReal.ofReal (B ^ 2) := by gcongr
    _ = ENNReal.ofReal (((2 + H1) * B) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        ring

/-- Pulls back the band `cellMeasure c` difference integral of `periodize c W` for any small
nonzero shift `h` (`|h| ≤ min 1 (σ / 2)`) to the positive-shift `δ = |h|` chart integral of `b`
over `Icc (σ / 2) H1 × B0579.cell c`. -/
theorem integral_cut_periodize_diff_le_band_chart {c σ H1 L1 h : ℝ}
    (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {W : HSpace c MeridC} {b : Chart → Fin 2 → ℂ}
    (hbv : b =ᵐ[ageμ c (-3 / 2)] velF c W)
    (hbm : ∀ i, Measurable fun p => b p i)
    (hh : |h| ≤ min 1 (σ / 2)) (hh0 : h ≠ 0) :
    ENNReal.ofReal (∫ p, ‖χ (shiftS h p) •
        (periodize c (W : Profile → MeridC) (shiftS h p) -
          periodize c (W : Profile → MeridC) p)‖ ^ 2 ∂(cellMeasure c)) ≤
      ENNReal.ofReal (cNorm8 χ ^ 2) *
        ∫⁻ s in Icc (σ / 2) H1,
          ∫⁻ y in B0579.cell c,
            ENNReal.ofReal (vnorm2 (fun i => b (s + |h|, y) i - b (s, y) i) ^ 2) := by
  set δ := |h|
  have hδ0 : 0 < δ := abs_pos.2 hh0
  have hδ_σ2 : δ ≤ σ / 2 := hh.trans (min_le_right 1 (σ / 2))
  have hσ2 : 0 < σ / 2 := half_pos hσ
  have hσH' : σ / 2 ≤ H1 + 1 := by linarith
  -- Integrability of `‖u1‖^2` on `cellMeasure c`
  let diff : Profile → MeridC := fun p =>
    flatStressCutRep c χ W (shiftS h p) - flatStressCutRep c χ W p
  let u1 : Profile → MeridC := fun p =>
    χ (shiftS h p) • (periodize c (W : Profile → MeridC) (shiftS h p) -
      periodize c (W : Profile → MeridC) p)
  let u2 : Profile → MeridC := fun p =>
    (χ (shiftS h p) - χ p) • periodize c (W : Profile → MeridC) p
  have hdiff_cut := isNearCutoff_diffCutoff hσ hχ hh
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
    memLp_flatStressCutRep hc hσ2 hσH' hdiff_cut hdiff_cut.smooth.continuous.measurable W
  have hu1_eq : u1 = diff - u2 := by
    funext p
    simp only [u1, diff, u2, flatStressCutRep, Pi.sub_apply]
    rw [smul_sub, sub_smul, sub_sub_sub_cancel_right]
  have hint1 : Integrable (fun p => ‖u1 p‖ ^ 2) (cellMeasure c) := by
    have hmem1 : MemLp u1 2 (cellMeasure c) := by rw [hu1_eq]; exact hmem_diff.sub hmem2
    exact hmem1.integrable_norm_pow two_ne_zero
  -- Positive-shift band indicator `Ψ` on `Profile`
  let B_set : Set Profile := {p : Profile | p.1 ∈ Icc (σ / 2) H1}
  have hB_meas : MeasurableSet B_set := measurableSet_Icc.preimage measurable_fst
  have hm_per : Measurable (periodize c (W : Profile → MeridC)) :=
    measurable_periodize_meridC c (Lp.stronglyMeasurable W).measurable
  let Ψ : Profile → ℝ≥0∞ := B_set.indicator fun q =>
    ENNReal.ofReal (‖periodize c (W : Profile → MeridC) (shiftS δ q) -
      periodize c (W : Profile → MeridC) q‖ ^ 2)
  have hΨ_meas : Measurable Ψ :=
    (ENNReal.measurable_ofReal.comp
      ((((hm_per.comp (measurable_shiftS δ)).sub hm_per).norm).pow_const 2)).indicator hB_meas
  have hΨ_supp : ∀ p : Profile, p.1 ≤ 0 → Ψ p = 0 := fun p hp0 => by
    dsimp only [Ψ]
    refine indicator_of_notMem (fun hpB => ?_) _
    have : σ / 2 ≤ p.1 := hpB.1
    linarith
  -- Step A: bound `∫⁻ ofReal (‖u1‖^2) ∂(cellMeasure c)` by `ofReal (cNorm8 χ ^ 2) * ∫⁻ Ψ`
  have hStepA : ∫⁻ p, ENNReal.ofReal (‖u1 p‖ ^ 2) ∂(cellMeasure c) ≤
      ENNReal.ofReal (cNorm8 χ ^ 2) * ∫⁻ p, Ψ p ∂(cellMeasure c) := by
    rcases lt_or_gt_of_ne hh0 with hh_neg | hh_pos
    · have hδ_eq : δ = -h := abs_of_neg hh_neg
      have hpt : ∀ p : Profile,
          ENNReal.ofReal (‖u1 p‖ ^ 2) ≤ ENNReal.ofReal (cNorm8 χ ^ 2) * Ψ (shiftS h p) := by
        intro p
        by_cases hχ0 : χ (shiftS h p) = 0
        · have hu0 : u1 p = 0 := by simp [u1, hχ0]
          rw [hu0, norm_zero, zero_pow two_ne_zero, ENNReal.ofReal_zero]
          exact zero_le
        · obtain ⟨hs1, hs2, _⟩ := hχ.support (shiftS h p) hχ0
          have hpB : shiftS h p ∈ B_set := ⟨by linarith, hs2⟩
          have hinv : shiftS δ (shiftS h p) = p := by
            rcases p with ⟨s, q, η⟩
            simp [shiftS, hδ_eq]
          have hnorm_u1 : ‖u1 p‖ ^ 2 ≤ cNorm8 χ ^ 2 *
              ‖periodize c (W : Profile → MeridC) (shiftS δ (shiftS h p)) -
                periodize c (W : Profile → MeridC) (shiftS h p)‖ ^ 2 := by
            dsimp only [u1]
            rw [hinv, norm_smul, Real.norm_eq_abs, mul_pow,
              norm_sub_rev (periodize c (W : Profile → MeridC) p)]
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (abs_nonneg _) (abs_le_cNorm8_of_nearCutoff hc hχ (shiftS h p)) 2)
              (sq_nonneg _)
          dsimp only [Ψ]
          rw [indicator_of_mem hpB, ← ENNReal.ofReal_mul (sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hnorm_u1
      calc ∫⁻ p, ENNReal.ofReal (‖u1 p‖ ^ 2) ∂(cellMeasure c)
          ≤ ∫⁻ p, ENNReal.ofReal (cNorm8 χ ^ 2) * Ψ (shiftS h p) ∂(cellMeasure c) :=
            lintegral_mono hpt
        _ = ENNReal.ofReal (cNorm8 χ ^ 2) * ∫⁻ p, Ψ (shiftS h p) ∂(cellMeasure c) :=
            lintegral_const_mul _ (hΨ_meas.comp (measurable_shiftS h))
        _ ≤ ENNReal.ofReal (cNorm8 χ ^ 2) * ∫⁻ p, Ψ p ∂(cellMeasure c) :=
            mul_le_mul' le_rfl (lintegral_shiftS_le c h hΨ_meas hΨ_supp)
    · have hδ_eq : δ = h := abs_of_pos hh_pos
      have hpt : ∀ p : Profile,
          ENNReal.ofReal (‖u1 p‖ ^ 2) ≤ ENNReal.ofReal (cNorm8 χ ^ 2) * Ψ p := by
        intro p
        by_cases hχ0 : χ (shiftS h p) = 0
        · have hu0 : u1 p = 0 := by simp [u1, hχ0]
          rw [hu0, norm_zero, zero_pow two_ne_zero, ENNReal.ofReal_zero]
          exact zero_le
        · obtain ⟨hs1, hs2, _⟩ := hχ.support (shiftS h p) hχ0
          change σ ≤ p.1 + h at hs1
          change p.1 + h ≤ H1 at hs2
          have hpB : p ∈ B_set := ⟨by linarith, by linarith⟩
          have hnorm_u1 : ‖u1 p‖ ^ 2 ≤ cNorm8 χ ^ 2 *
              ‖periodize c (W : Profile → MeridC) (shiftS δ p) -
                periodize c (W : Profile → MeridC) p‖ ^ 2 := by
            dsimp only [u1]
            rw [hδ_eq, norm_smul, Real.norm_eq_abs, mul_pow]
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (abs_nonneg _) (abs_le_cNorm8_of_nearCutoff hc hχ (shiftS h p)) 2)
              (sq_nonneg _)
          dsimp only [Ψ]
          rw [indicator_of_mem hpB, ← ENNReal.ofReal_mul (sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hnorm_u1
      calc ∫⁻ p, ENNReal.ofReal (‖u1 p‖ ^ 2) ∂(cellMeasure c)
          ≤ ∫⁻ p, ENNReal.ofReal (cNorm8 χ ^ 2) * Ψ p ∂(cellMeasure c) :=
            lintegral_mono hpt
        _ = ENNReal.ofReal (cNorm8 χ ^ 2) * ∫⁻ p, Ψ p ∂(cellMeasure c) :=
            lintegral_const_mul _ hΨ_meas
  -- Step B: transport `∫⁻ Ψ ∂(cellMeasure c)` to `Icc (σ / 2) H1 × B0579.cell c` via `cellPtInv`
  let S : Set Chart := Ioi (0 : ℝ) ×ˢ B0579.cell c
  let S_band : Set Chart := Icc (σ / 2) H1 ×ˢ B0579.cell c
  have hSm : MeasurableSet S := measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hSbm : MeasurableSet S_band := measurableSet_Icc.prod (B0579.measurableSet_cell c)
  have hSb_sub : S_band ⊆ S := prod_mono (fun s hs => lt_of_lt_of_le hσ2 hs.1) subset_rfl
  have hmap : Measure.map (cellPtInv c) (volume.restrict S) = cellMeasure c :=
    N01.cellPtInv_map hc
  have hcellPtInv_mem : ∀ z ∈ S, cellPtInv c z ∈ cell c := by
    rintro ⟨s, q, η⟩ ⟨hs, ⟨hq1, hq2⟩, _⟩
    refine ⟨hs, ?_, trivial⟩
    change N01.ctInvT c q ∈ Ioc 0 c
    unfold N01.ctInvT
    split_ifs with hq0
    · exact ⟨hq0, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hb_S : ∀ᵐ z : ℝ × (ℝ × ℝ) ∂volume, z ∈ S → b z = velF c (W : Profile → MeridC) z :=
    (ae_restrict_iff' hSm).1 ((volCyl_ac_ageμ hc (-3 / 2)).ae_le hbv)
  have hmp_shift : MeasurePreserving (fun z : ℝ × (ℝ × ℝ) => (z.1 + δ, z.2)) volume volume := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    exact (measurePreserving_add_right volume δ).prod ⟨measurable_id, Measure.map_id⟩
  have hb_S_shift : ∀ᵐ z : ℝ × (ℝ × ℝ) ∂volume,
      (z.1 + δ, z.2) ∈ S → b (z.1 + δ, z.2) = velF c (W : Profile → MeridC) (z.1 + δ, z.2) :=
    hmp_shift.quasiMeasurePreserving.ae hb_S
  have hΨ_eq_chart : ∫⁻ p, Ψ p ∂(cellMeasure c) =
      ∫⁻ s in Icc (σ / 2) H1,
        ∫⁻ y in B0579.cell c,
          ENNReal.ofReal (vnorm2 (fun i => b (s + δ, y) i - b (s, y) i) ^ 2) := by
    rw [← hmap, lintegral_map hΨ_meas (measurable_cellPtInv c)]
    have hind_eq : ∀ z ∈ S, Ψ (cellPtInv c z) =
        S_band.indicator (fun w => ENNReal.ofReal
          (‖periodize c (W : Profile → MeridC) (shiftS δ (cellPtInv c w)) -
            periodize c (W : Profile → MeridC) (cellPtInv c w)‖ ^ 2)) z := by
      rintro ⟨s, y⟩ ⟨hs, hy⟩
      have hf1 : (cellPtInv c (s, y)).1 = s := rfl
      by_cases hsB : s ∈ Icc (σ / 2) H1
      · have h1 : cellPtInv c (s, y) ∈ B_set := by simpa [B_set, hf1] using hsB
        have h2 : (s, y) ∈ S_band := ⟨hsB, hy⟩
        dsimp only [Ψ]
        rw [indicator_of_mem h1, indicator_of_mem h2]
      · have h1 : cellPtInv c (s, y) ∉ B_set := by simpa [B_set, hf1] using hsB
        have h2 : (s, y) ∉ S_band := fun h => hsB h.1
        dsimp only [Ψ]
        rw [indicator_of_notMem h1, indicator_of_notMem h2]
    rw [setLIntegral_congr_fun hSm hind_eq, lintegral_indicator hSbm,
      Measure.restrict_restrict hSbm, inter_eq_left.2 hSb_sub]
    have hae_band : ∀ᵐ z ∂(volume.restrict S_band),
        ENNReal.ofReal (‖periodize c (W : Profile → MeridC) (shiftS δ (cellPtInv c z)) -
            periodize c (W : Profile → MeridC) (cellPtInv c z)‖ ^ 2) =
          ENNReal.ofReal (vnorm2 (fun i => b (z.1 + δ, z.2) i - b z i) ^ 2) := by
      rw [ae_restrict_iff' hSbm]
      filter_upwards [hb_S, hb_S_shift] with z hbz hbzd hzB
      rcases z with ⟨s, q, η⟩
      have hzS : (s, q, η) ∈ S := hSb_sub hzB
      have hzdS : (s + δ, q, η) ∈ S :=
        ⟨show 0 < s + δ by linarith [hzB.1.1], hzB.2⟩
      have hshift_inv : shiftS δ (cellPtInv c (s, q, η)) = cellPtInv c (s + δ, q, η) := rfl
      rw [hshift_inv, periodize_of_mem hc _ (hcellPtInv_mem _ hzdS),
        periodize_of_mem hc _ (hcellPtInv_mem _ hzS)]
      have hb1 : b (s, q, η) = velF c (W : Profile → MeridC) (s, q, η) := hbz hzS
      have hb2 : b (s + δ, q, η) = velF c (W : Profile → MeridC) (s + δ, q, η) := hbzd hzdS
      congr 2
      rw [hb1, hb2, fsf_vnorm2_eq_norm]
      rfl
    rw [lintegral_congr_ae hae_band]
    have hdiff_m : ∀ i, Measurable fun z : Chart => b (z.1 + δ, z.2) i - b z i := fun i =>
      ((hbm i).comp ((measurable_fst.add_const δ).prodMk measurable_snd)).sub (hbm i)
    have hf_m : Measurable fun z : Chart =>
        ENNReal.ofReal (vnorm2 (fun i => b (z.1 + δ, z.2) i - b z i) ^ 2) :=
      ENNReal.measurable_ofReal.comp
        ((UnforcedLeray.Short.IIIa.loc_measurable_vnorm2 hdiff_m).pow_const 2)
    exact UnforcedLeray.Short.IIIa.lintegral_restrict_prod_eq
      (Icc (σ / 2) H1) (B0579.cell c) _ hf_m
  rw [ofReal_integral_eq_lintegral_ofReal hint1 (Eventually.of_forall fun _ => sq_nonneg _),
    ← hΨ_eq_chart]
  exact hStepA

end N05_4_2BandAux

open N05_4_2BandAux

/-- **Unconditional proof of `FlatBandAgeDiffQuotient` (`PartII-a:N05/4/2/1`)** with `k = 5`,
`C = 6`. -/
theorem flatBandAgeDiffQuotient : FlatBandAgeDiffQuotient := by
  refine ⟨5, 6, by norm_num, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hm μ hμM hμγ
    M_test hM_test x G _hx _hG b Gr hbv hsol hW_le hCal_Gr hCal_F h hh
  by_cases hh0 : h = 0
  · subst hh0
    have hzero : ∀ p : Profile, shiftS 0 p = p := by
      rintro ⟨s, q, η⟩; simp [shiftS]
    simp [hzero]
  set δ := |h|
  have hδ0 : 0 < δ := abs_pos.2 hh0
  have hδ1 : δ ≤ 1 := hh.trans (min_le_left 1 (σ / 2))
  set W := T0flat hc ν μ G
  set F := tblkF c M_test
  -- Build `FreeSolData c ν μ F b Gr`
  have hFm : ∀ i j, Measurable fun p => F p i j :=
    fun i j => fsf_measurable_tblkF hM_test.smooth.continuous.measurable i j
  have hF_fin : tCalNorm c F < ⊤ := by
    have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    have h1 := lt_of_le_of_lt hCal_F ENNReal.ofReal_lt_top
    rcases ENNReal.mul_lt_top_iff.1 h1 with hlt | hzero | hzero
    · exact hlt.2
    · exact absurd hzero (by rw [ENNReal.ofReal_eq_zero, not_le]; exact hsc)
    · rw [hzero]; exact ENNReal.zero_lt_top
  have hFl := UnforcedLeray.Short.IIIa.gainLocF c ν 0 hc le_rfl hν F hFm
    (by simpa [fsf_gainConj_zero] using hF_fin)
  simp only [fsf_gainConj_zero] at hFl
  have hS : FreeSolData c ν μ F b Gr :=
    { pos_c := hc
      pos_ν := hν
      meas := hFm
      l2loc := fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).1
      sol := hsol }
  -- Local finiteness for `b` and `Gr` from `hsol.energyLoc`
  have hBG_loc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2) < ⊤) ∧
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (Gr p) ^ 2) < ⊤) := by
    intro s₁ s₂ h1 h2
    have he := hsol.energyLoc s₁ s₂ h1 h2
    constructor
    · refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_) he
      linarith [sq_nonneg (tnorm2 (Gr p))]
    · refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_) he
      linarith [sq_nonneg (vnorm2 (b p))]
  -- Band integral bounds on `Icc (σ / 2) (H1 + 1)`
  have hIntE_le : ∫ s in Icc (σ / 2) (H1 + 1), energyE c b s ≤ ((2 + H1) * ‖W‖) ^ 2 :=
    integral_energyE_band_le hc hσ hσH hbv hsol.measurable (fun s₁ s₂ h1 h2 => (hBG_loc s₁ s₂ h1 h2).1)
  have hIntGr_le : ∫ s in Icc (σ / 2) (H1 + 1), energyN c Gr s ≤
      ((2 + H1) * (ν⁻¹ * (Real.sqrt 2 * ‖x‖))) ^ 2 :=
    integral_energyN_band_le hc hσ hσH (by positivity) hsol.gradMeasurable
      (fun s₁ s₂ h1 h2 => (hBG_loc s₁ s₂ h1 h2).2) hCal_Gr
  have hIntF_le : ∫ s in Icc (σ / 2) (H1 + 1), energyN c F s ≤
      ((2 + H1) * (Real.sqrt 2 * ‖x‖)) ^ 2 :=
    integral_energyN_band_le hc hσ hσH (by positivity) hFm
      (fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2) hCal_F
  -- Combine pullback + `lintegral_band_diff_le`
  have hpull := integral_cut_periodize_diff_le_band_chart hc hσ hσH hχ hm hbv hsol.measurable hh hh0
  have hstek := lintegral_band_diff_le hS hσ hσH hμM hδ0 hδ1
  obtain ⟨hIntE, hIntN, hIntF⟩ :=
    UnforcedLeray.Short.IIIa.lmEnergyLocInt c ν μ F b Gr hS (σ / 2) (H1 + 1)
      (half_pos hσ) (by linarith)
  have hA0 : 0 ≤ 2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F Gr b t :=
    mul_nonneg zero_le_two (integral_nonneg fun t => show 0 ≤ bandASq c ν σ M F Gr b t by
      unfold bandASq
      have : 0 ≤ energyE c b t := integral_nonneg fun _ => sq_nonneg _
      have : 0 ≤ energyN c Gr t := integral_nonneg fun _ => sq_nonneg _
      have : 0 ≤ energyN c F t := integral_nonneg fun _ => sq_nonneg _
      positivity)
  have hB0 : 0 ≤ 2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c Gr b r :=
    mul_nonneg zero_le_two (integral_nonneg fun r => show 0 ≤ bandBSq c Gr b r by
      unfold bandBSq
      have : 0 ≤ energyE c b r := integral_nonneg fun _ => sq_nonneg _
      have : 0 ≤ energyN c Gr r := integral_nonneg fun _ => sq_nonneg _
      positivity)
  have hcomb_enn : ENNReal.ofReal (∫ p, ‖χ (shiftS h p) •
        (periodize c (W : Profile → MeridC) (shiftS h p) -
          periodize c (W : Profile → MeridC) p)‖ ^ 2 ∂(cellMeasure c)) ≤
      ENNReal.ofReal (cNorm8 χ ^ 2 * (δ *
        ((2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F Gr b t) +
          2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c Gr b r))) := by
    calc ENNReal.ofReal (∫ p, ‖χ (shiftS h p) •
            (periodize c (W : Profile → MeridC) (shiftS h p) -
              periodize c (W : Profile → MeridC) p)‖ ^ 2 ∂(cellMeasure c))
        ≤ ENNReal.ofReal (cNorm8 χ ^ 2) *
            ENNReal.ofReal (δ * ((2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F Gr b t) +
              2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c Gr b r)) :=
          hpull.trans (by gcongr)
      _ = ENNReal.ofReal (cNorm8 χ ^ 2 * (δ *
            ((2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F Gr b t) +
              2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c Gr b r))) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  have hcomb_real : ∫ p, ‖χ (shiftS h p) •
        (periodize c (W : Profile → MeridC) (shiftS h p) -
          periodize c (W : Profile → MeridC) p)‖ ^ 2 ∂(cellMeasure c) ≤
      cNorm8 χ ^ 2 * (δ *
        ((2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F Gr b t) +
          2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c Gr b r)) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _)
      (mul_nonneg hδ0.le (add_nonneg hA0 hB0)))).1 hcomb_enn
  -- Absorb all factors into `(6 * Gamma ^ 5 * ‖x‖) ^ 2 * |h|`
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ Gam := gamma_ge_one χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have hγi : 0 < γs⁻¹ := inv_pos.2 hγ
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have h2H1_G : 2 + H1 ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hM_G : M ≤ Gam := by
    unfold Gam Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hσ_G : σ⁻¹ ≤ Gam := by
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
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  -- Constituent bounds in powers of `Gam`
  have hW_Gam : (2 + H1) * ‖W‖ ≤ Gam ^ 2 * ‖x‖ := by
    calc (2 + H1) * ‖W‖
        ≤ (2 + H1) * ((Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖x‖) :=
          mul_le_mul_of_nonneg_left hW_le (by linarith)
      _ = (2 + H1) * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖x‖ := by ring
      _ ≤ (Gam * Gam) * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          exact mul_le_mul h2H1_G hsqrt_le (by positivity) hG0
      _ = Gam ^ 2 * ‖x‖ := by ring
  have hE_Gam : ∫ s in Icc (σ / 2) (H1 + 1), energyE c b s ≤ (Gam ^ 2 * ‖x‖) ^ 2 :=
    hIntE_le.trans (pow_le_pow_left₀ (mul_nonneg (by linarith) (norm_nonneg W)) hW_Gam 2)
  have hGr_Gam : ∫ s in Icc (σ / 2) (H1 + 1), energyN c Gr s ≤ (2 * Gam ^ 2 * ‖x‖) ^ 2 := by
    have hb : (2 + H1) * (ν⁻¹ * (Real.sqrt 2 * ‖x‖)) ≤ 2 * Gam ^ 2 * ‖x‖ := by
      calc (2 + H1) * (ν⁻¹ * (Real.sqrt 2 * ‖x‖))
          ≤ (2 + H1) * (ν⁻¹ * (2 * ‖x‖)) := by gcongr
        _ = 2 * ((2 + H1) * ν⁻¹) * ‖x‖ := by ring
        _ ≤ 2 * (Gam * Gam) * ‖x‖ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ zero_le_two)
              (norm_nonneg x)
            exact mul_le_mul h2H1_G hν_G hνi.le hG0
        _ = 2 * Gam ^ 2 * ‖x‖ := by ring
    exact hIntGr_le.trans (pow_le_pow_left₀ (by positivity) hb 2)
  have hνGr_Gam : ν ^ 2 * ∫ s in Icc (σ / 2) (H1 + 1), energyN c Gr s ≤ (2 * Gam ^ 4 * ‖x‖) ^ 2 := by
    have h1 : ν ^ 2 * ((2 + H1) * (ν⁻¹ * (Real.sqrt 2 * ‖x‖))) ^ 2 =
        ((2 + H1) * (Real.sqrt 2 * ‖x‖)) ^ 2 := by
      have hν_inv : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν.ne'
      calc ν ^ 2 * ((2 + H1) * (ν⁻¹ * (Real.sqrt 2 * ‖x‖))) ^ 2
          = ((ν * ν⁻¹) * ((2 + H1) * (Real.sqrt 2 * ‖x‖))) ^ 2 := by ring
        _ = ((2 + H1) * (Real.sqrt 2 * ‖x‖)) ^ 2 := by rw [hν_inv, one_mul]
    have hb : (2 + H1) * (Real.sqrt 2 * ‖x‖) ≤ 2 * Gam ^ 4 * ‖x‖ := by
      have hG14 : Gam ≤ Gam ^ 4 := by
        simpa using pow_le_pow_right₀ hG1 (by omega : 1 ≤ 4)
      calc (2 + H1) * (Real.sqrt 2 * ‖x‖)
          ≤ (2 + H1) * (2 * ‖x‖) := by gcongr
        _ = 2 * (2 + H1) * ‖x‖ := by ring
        _ ≤ 2 * Gam ^ 4 * ‖x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
            linarith
    calc ν ^ 2 * ∫ s in Icc (σ / 2) (H1 + 1), energyN c Gr s
        ≤ ν ^ 2 * ((2 + H1) * (ν⁻¹ * (Real.sqrt 2 * ‖x‖))) ^ 2 :=
          mul_le_mul_of_nonneg_left hIntGr_le (sq_nonneg ν)
      _ = ((2 + H1) * (Real.sqrt 2 * ‖x‖)) ^ 2 := h1
      _ ≤ (2 * Gam ^ 4 * ‖x‖) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
  have hF_Gam : ∫ s in Icc (σ / 2) (H1 + 1), energyN c F s ≤ (2 * Gam ^ 4 * ‖x‖) ^ 2 := by
    have hb : (2 + H1) * (Real.sqrt 2 * ‖x‖) ≤ 2 * Gam ^ 4 * ‖x‖ := by
      have hG14 : Gam ≤ Gam ^ 4 := by
        simpa using pow_le_pow_right₀ hG1 (by omega : 1 ≤ 4)
      calc (2 + H1) * (Real.sqrt 2 * ‖x‖)
          ≤ (2 + H1) * (2 * ‖x‖) := by gcongr
        _ = 2 * (2 + H1) * ‖x‖ := by ring
        _ ≤ 2 * Gam ^ 4 * ‖x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
            linarith
    exact hIntF_le.trans (pow_le_pow_left₀ (by positivity) hb 2)
  have hdrift_Gam : (2 * M * σ⁻¹) ^ 2 * ∫ s in Icc (σ / 2) (H1 + 1), energyE c b s ≤
      (2 * Gam ^ 4 * ‖x‖) ^ 2 := by
    have hcoef : 2 * M * σ⁻¹ ≤ 2 * Gam ^ 2 := by
      have h1 : M * σ⁻¹ ≤ Gam * Gam := mul_le_mul hM_G hσ_G hσi.le hG0
      linarith [show Gam * Gam = Gam ^ 2 by ring]
    have hcoef_sq : (2 * M * σ⁻¹) ^ 2 ≤ (2 * Gam ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcoef 2
    have hE0 : 0 ≤ ∫ s in Icc (σ / 2) (H1 + 1), energyE c b s :=
      integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
    calc (2 * M * σ⁻¹) ^ 2 * ∫ s in Icc (σ / 2) (H1 + 1), energyE c b s
        ≤ (2 * Gam ^ 2) ^ 2 * (Gam ^ 2 * ‖x‖) ^ 2 :=
          mul_le_mul hcoef_sq hE_Gam hE0 (sq_nonneg _)
      _ = (2 * Gam ^ 4 * ‖x‖) ^ 2 := by ring
  -- Expand `∫ bandASq` and `∫ bandBSq`
  have hIntA_eq : ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F Gr b t =
      (2 * M * σ⁻¹) ^ 2 * (∫ t in Icc (σ / 2) (H1 + 1), energyE c b t) +
        ν ^ 2 * (∫ t in Icc (σ / 2) (H1 + 1), energyN c Gr t) +
        ∫ t in Icc (σ / 2) (H1 + 1), energyN c F t := by
    have h12 : IntegrableOn (fun t => (2 * M * σ⁻¹) ^ 2 * energyE c b t + ν ^ 2 * energyN c Gr t)
        (Icc (σ / 2) (H1 + 1)) := (hIntE.const_mul _).add (hIntN.const_mul _)
    unfold bandASq
    rw [integral_add h12 hIntF, integral_add (hIntE.const_mul _) (hIntN.const_mul _),
      integral_const_mul, integral_const_mul]
  have hIntB_eq : ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c Gr b r =
      (∫ r in Icc (σ / 2) (H1 + 1), energyE c b r) +
        ∫ r in Icc (σ / 2) (H1 + 1), energyN c Gr r :=
    integral_add hIntE hIntN
  have hG48 : Gam ^ 4 ≤ Gam ^ 8 := pow_le_pow_right₀ hG1 (by omega : 4 ≤ 8)
  have hsum_AB : (2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F Gr b t) +
      2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c Gr b r ≤
      36 * (Gam ^ 8 * ‖x‖ ^ 2) := by
    rw [hIntA_eq, hIntB_eq]
    have hr4 : (2 * Gam ^ 4 * ‖x‖) ^ 2 = 4 * (Gam ^ 8 * ‖x‖ ^ 2) := by ring
    have hrE : (Gam ^ 2 * ‖x‖) ^ 2 ≤ Gam ^ 8 * ‖x‖ ^ 2 := by
      calc (Gam ^ 2 * ‖x‖) ^ 2 = Gam ^ 4 * ‖x‖ ^ 2 := by ring
        _ ≤ Gam ^ 8 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hG48 (sq_nonneg ‖x‖)
    have hrG : (2 * Gam ^ 2 * ‖x‖) ^ 2 ≤ 4 * (Gam ^ 8 * ‖x‖ ^ 2) := by
      calc (2 * Gam ^ 2 * ‖x‖) ^ 2 = 4 * (Gam ^ 4 * ‖x‖ ^ 2) := by ring
        _ ≤ 4 * (Gam ^ 8 * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hG48 (sq_nonneg ‖x‖)) (by norm_num)
    have h0x : 0 ≤ Gam ^ 8 * ‖x‖ ^ 2 := mul_nonneg (pow_nonneg hG0 8) (sq_nonneg ‖x‖)
    rw [hr4] at hdrift_Gam hνGr_Gam hF_Gam
    have hE_Gam8 : ∫ s in Icc (σ / 2) (H1 + 1), energyE c b s ≤ Gam ^ 8 * ‖x‖ ^ 2 :=
      hE_Gam.trans hrE
    have hGr_Gam8 : ∫ s in Icc (σ / 2) (H1 + 1), energyN c Gr s ≤ 4 * (Gam ^ 8 * ‖x‖ ^ 2) :=
      hGr_Gam.trans hrG
    linarith
  have hcN_sq : cNorm8 χ ^ 2 ≤ Gam ^ 2 :=
    pow_le_pow_left₀ (cNorm8_nonneg χ) hcN_G 2
  calc ∫ p, ‖χ (shiftS h p) •
          (periodize c (W : Profile → MeridC) (shiftS h p) -
            periodize c (W : Profile → MeridC) p)‖ ^ 2 ∂(cellMeasure c)
      ≤ cNorm8 χ ^ 2 * (δ *
          ((2 * ∫ t in Icc (σ / 2) (H1 + 1), bandASq c ν σ M F Gr b t) +
            2 * ∫ r in Icc (σ / 2) (H1 + 1), bandBSq c Gr b r)) := hcomb_real
    _ ≤ Gam ^ 2 * (δ * (36 * (Gam ^ 8 * ‖x‖ ^ 2))) := by
        refine mul_le_mul hcN_sq ?_ (mul_nonneg hδ0.le (add_nonneg hA0 hB0)) (sq_nonneg Gam)
        exact mul_le_mul_of_nonneg_left hsum_AB hδ0.le
    _ = (6 * Gam ^ 5 * ‖x‖) ^ 2 * |h| := by
        dsimp [δ]
        ring

end UnforcedLeray.Short.PartIIa
