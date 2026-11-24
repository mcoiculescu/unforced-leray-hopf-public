import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14.StressEpsCommutingFlowShiftQ.CutoffShift
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Age (`shiftS`) leaf `PhaseHalfDriftCutoffShiftS` for `PartII-a:N05/3/1`

Source of record: `the November 2 reference manuscript`,
lines 1752–1756, 1769–1773 (`near:local-smoothing`).

Proves `phaseHalfDriftCutoffShiftS : PhaseHalfDriftCutoffShiftS` via:
1. `lintegral_Ioo_measureH_exp_age_sub_sq_le` (Step A): combines the dilation pullback
   `lintegral_measureH_exp_age_sub_sq_eq` and the Slobodeckij half-drift bound
   `lintegral_Ioi_phaseDilation_sub_sq_le` with the `e^{t/4} - 1` commutator.
2. `setLIntegral_Icc_Ioo_sliceDiffSq_le` (Step B): changes variables `u = (e^t - 1) s` on
   `s ∈ [σ/4, H1 + 2]` via `lintegral_image_eq_lintegral_abs_deriv_mul`, absorbs `s⁻¹` into
   `(2 + H1) s^{-3/2}` (`weightH`), and swaps integrals to reduce to Step A.
3. `setLIntegral_age_pos_shift_le` (Step C): averages the split `s + δ = (s + u) + (δ - u)` over
   `u ∈ Ioo 0 δ` to convert the Slobodeckij integral of Step B into the pointwise `L²` difference
   `∫⁻ s in [σ/4, H1 + 1], sliceDiffSq c b s δ ≤ 4 δ * (...)`.
4. `phaseHalfDriftCutoffShiftS` (Step D): handles `h = 0`, large shifts `|h| ≥ min (1/4) (σ/4)`,
   and small shifts `0 < |h| < min (1/4) (σ/4)` (reducing `h < 0` to `δ = |h| > 0` by translating
   `s ↦ s + h`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N05FlowAux

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp UnforcedLeray.FreeStress
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open N05_1Aux N05_3Aux N05_4Aux N05_3_1Aux

/-! ### 0. One-dimensional `lintegral` change-of-variables helpers -/

private theorem two_term_enorm_sq_le (x y : MeridC) :
    ‖x + y‖ₑ ^ (2 : ℝ) ≤ 2 * ‖x‖ₑ ^ (2 : ℝ) + 2 * ‖y‖ₑ ^ (2 : ℝ) := by
  have hreal : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have htri : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    have hsq : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have h1 : ‖x + y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖x + y‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have h2 : 2 * ‖x‖ₑ ^ (2 : ℝ) + 2 * ‖y‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, ← ofReal_norm, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two, Real.rpow_two]
  rw [h1, h2]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem setLIntegral_Icc_add_right_le {a b c d : ℝ} (u : ℝ)
    (ha : c ≤ a + u) (hb : b + u ≤ d) (g : ℝ → ℝ≥0∞) :
    ∫⁻ s in Icc a b, g (s + u) ≤ ∫⁻ s in Icc c d, g s := by
  let φ : ℝ → ℝ := fun s => s + u
  have hd : ∀ s ∈ Icc a b, HasDerivWithinAt φ 1 (Icc a b) s :=
    fun s _ => by simpa [φ] using ((hasDerivAt_id s).add_const u).hasDerivWithinAt
  have hinj : InjOn φ (Icc a b) := fun s₁ _ s₂ _ h => by dsimp [φ] at h; linarith
  have himg := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hd hinj g
  have hsub : φ '' Icc a b ⊆ Icc c d := by
    rintro _ ⟨s, ⟨hs1, hs2⟩, rfl⟩
    exact ⟨by dsimp [φ]; linarith, by dsimp [φ]; linarith⟩
  have hrhs : ∫⁻ s in Icc a b, ENNReal.ofReal |(1 : ℝ)| * g (φ s) =
      ∫⁻ s in Icc a b, g (s + u) := by
    simp [φ]
  rw [← hrhs, ← himg]
  exact lintegral_mono_set hsub

private theorem setLIntegral_Ioo_sub_left_eq {δ : ℝ} (g : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioo 0 δ, g (δ - u) = ∫⁻ u in Ioo 0 δ, g u := by
  let ψ : ℝ → ℝ := fun u => δ - u
  have hd : ∀ u ∈ Ioo 0 δ, HasDerivWithinAt ψ (-1) (Ioo 0 δ) u :=
    fun u _ => (hasDerivWithinAt_id u (Ioo 0 δ)).const_sub δ
  have hinj : InjOn ψ (Ioo 0 δ) := fun u₁ _ u₂ _ h => by dsimp [ψ] at h; linarith
  have himg := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj g
  have him_eq : ψ '' Ioo 0 δ = Ioo 0 δ := by
    ext v
    simp only [mem_image, mem_Ioo, ψ]
    constructor
    · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hv1, hv2⟩
      exact ⟨δ - v, ⟨by linarith, by linarith⟩, by ring⟩
  rw [him_eq] at himg
  symm
  refine himg.trans ?_
  simp [ψ]

private theorem setLIntegral_Ioo_exp_sub_one_mul_le {s δ : ℝ} (hs : 0 < s) (hδs : δ ≤ s)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioo 0 δ, ENNReal.ofReal (u ^ (-2 : ℝ)) * g u ≤
      ENNReal.ofReal (Real.exp 1 * s⁻¹) *
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (-2 : ℝ)) * g ((Real.exp t - 1) * s) := by
  let φ : ℝ → ℝ := fun t => (Real.exp t - 1) * s
  have hsub : Ioo 0 δ ⊆ φ '' Ioo (0 : ℝ) 1 := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hus : u < s := hu.2.trans_le hδs
    have hquot_pos : 0 < u / s := div_pos hu0 hs
    have hquot_lt1 : u / s < 1 := (div_lt_one hs).2 hus
    have harg_pos : 0 < 1 + u / s := by linarith
    have harg_lt_e : 1 + u / s < Real.exp 1 := by
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      linarith
    refine ⟨Real.log (1 + u / s), ⟨Real.log_pos (by linarith), ?_⟩, ?_⟩
    · calc Real.log (1 + u / s)
          < Real.log (Real.exp 1) := Real.log_lt_log harg_pos harg_lt_e
        _ = 1 := Real.log_exp 1
    · dsimp only [φ]
      rw [Real.exp_log harg_pos]
      have hs0 : s ≠ 0 := hs.ne'
      field_simp
      ring
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt φ (Real.exp t * s) (Ioo 0 1) t :=
    fun t _ => (((Real.hasDerivAt_exp t).sub_const 1).mul_const s).hasDerivWithinAt
  have hinj : InjOn φ (Ioo (0 : ℝ) 1) := by
    intro t₁ _ t₂ _ h
    dsimp only [φ] at h
    have h1 : Real.exp t₁ - 1 = Real.exp t₂ - 1 := mul_right_cancel₀ hs.ne' h
    exact Real.exp_injective (by linarith)
  have himg := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj
    (fun u => ENNReal.ofReal (u ^ (-2 : ℝ)) * g u)
  have h1 : ∫⁻ u in Ioo 0 δ, ENNReal.ofReal (u ^ (-2 : ℝ)) * g u ≤
      ∫⁻ t in Ioo (0 : ℝ) 1,
        ENNReal.ofReal |Real.exp t * s| *
          (ENNReal.ofReal ((φ t) ^ (-2 : ℝ)) * g (φ t)) :=
    (lintegral_mono_set hsub).trans himg.le
  refine h1.trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2.le
  have ht_le_exp : t ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  have hts_pos : 0 < t * s := mul_pos ht0 hs
  have hts_le_φ : t * s ≤ φ t := mul_le_mul_of_nonneg_right ht_le_exp hs.le
  have hrpow_le : (φ t) ^ (-2 : ℝ) ≤ t ^ (-2 : ℝ) * s ^ (-2 : ℝ) := by
    calc (φ t) ^ (-2 : ℝ)
        ≤ (t * s) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hts_pos hts_le_φ (by norm_num)
      _ = t ^ (-2 : ℝ) * s ^ (-2 : ℝ) := Real.mul_rpow ht0.le hs.le
  have hs_rpow : s * s ^ (-2 : ℝ) = s⁻¹ := by
    calc s * s ^ (-2 : ℝ)
        = s ^ (1 : ℝ) * s ^ (-2 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ ((1 : ℝ) + (-2)) := (Real.rpow_add hs 1 (-2)).symm
      _ = s⁻¹ := by rw [show (1 : ℝ) + (-2) = -1 by norm_num, Real.rpow_neg_one]
  have hjac_le : |Real.exp t * s| * (φ t) ^ (-2 : ℝ) ≤ (Real.exp 1 * s⁻¹) * t ^ (-2 : ℝ) := by
    have hjac_pos : 0 < Real.exp t * s := mul_pos (Real.exp_pos t) hs
    rw [abs_of_pos hjac_pos]
    have hexp_le : Real.exp t * s ≤ Real.exp 1 * s :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ht1) hs.le
    calc (Real.exp t * s) * (φ t) ^ (-2 : ℝ)
        ≤ (Real.exp 1 * s) * (t ^ (-2 : ℝ) * s ^ (-2 : ℝ)) :=
          mul_le_mul hexp_le hrpow_le (Real.rpow_nonneg (hts_pos.trans_le hts_le_φ).le _)
            (by positivity)
      _ = Real.exp 1 * (s * s ^ (-2 : ℝ)) * t ^ (-2 : ℝ) := by ring
      _ = (Real.exp 1 * s⁻¹) * t ^ (-2 : ℝ) := by rw [hs_rpow]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hjac_le) zero_le

/-! ### 1. Step A: Dilation Slobodeckij integral on `measureH c` -/

private theorem exp_age_diff_enorm_sq_le {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x y : MeridC) :
    ‖x - y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 * Real.exp 2) * ‖(Real.exp (-(t / 4)) : ℂ) • x - y‖ₑ ^ (2 : ℝ) +
        ENNReal.ofReal (2 * Real.exp 2 * t ^ 2) * ‖y‖ₑ ^ (2 : ℝ) := by
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2.le
  have hdecomp : x - y =
      (Real.exp (t / 4) : ℂ) • ((Real.exp (-(t / 4)) : ℂ) • x - y) +
        ((Real.exp (t / 4) - 1 : ℝ) : ℂ) • y := by
    have hmul : Real.exp (t / 4) * Real.exp (-(t / 4)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simp only [smul_sub, Complex.coe_smul, smul_smul, hmul, one_smul, sub_smul]
    abel
  rw [hdecomp]
  refine (two_term_enorm_sq_le _ _).trans ?_
  have hexp_sq : Real.exp (t / 4) ^ 2 ≤ Real.exp 2 := by
    rw [sq, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hmvt_sq : |Real.exp (t / 4) - 1| ^ 2 ≤ Real.exp 2 * t ^ 2 := by
    have ht4_abs : |t / 4| ≤ 1 := by
      rw [abs_of_pos (by positivity)]
      linarith
    have hm := abs_exp_sub_one_le (by norm_num : (0 : ℝ) ≤ 1) ht4_abs
    rw [abs_of_pos (by positivity : 0 < t / 4)] at hm
    have hm' : |Real.exp (t / 4) - 1| ≤ Real.exp 1 * t := by
      calc |Real.exp (t / 4) - 1|
          ≤ Real.exp 1 * (t / 4) := hm
        _ ≤ Real.exp 1 * t := by
            refine mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 1).le
    calc |Real.exp (t / 4) - 1| ^ 2
        ≤ (Real.exp 1 * t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hm' 2
      _ = Real.exp 1 ^ 2 * t ^ 2 := mul_pow _ _ 2
      _ = Real.exp 2 * t ^ 2 := by
          congr 1
          rw [sq, ← Real.exp_add]
          norm_num
  have hterm1 : (2 : ℝ≥0∞) *
      ‖(Real.exp (t / 4) : ℂ) • ((Real.exp (-(t / 4)) : ℂ) • x - y)‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 * Real.exp 2) * ‖(Real.exp (-(t / 4)) : ℂ) • x - y‖ₑ ^ (2 : ℝ) := by
    rw [Complex.coe_smul, ← ofReal_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (by norm_num),
      Real.rpow_two, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
      ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two,
      ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hexp_sq) zero_le
  have hterm2 : (2 : ℝ≥0∞) * ‖((Real.exp (t / 4) - 1 : ℝ) : ℂ) • y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 * Real.exp 2 * t ^ 2) * ‖y‖ₑ ^ (2 : ℝ) := by
    rw [Complex.coe_smul, ← ofReal_norm, norm_smul, Real.norm_eq_abs,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (by norm_num),
      Real.rpow_two, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
      ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two,
      ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    rw [show 2 * Real.exp 2 * t ^ 2 = 2 * (Real.exp 2 * t ^ 2) by ring,
      ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hmvt_sq) zero_le
  exact add_le_add hterm1 hterm2

private theorem lintegral_Ioo_measureH_exp_age_sub_sq_le {ε c P : ℝ} [Fact (0 < P)]
    (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2) (hU : N01.IsPhaseLift ε P U)
    (W : HSpace c MeridC) {w_hd : Yq P 2}
    (hw : (FreeStress.phaseC0 P).HasPow (1 / 2) (U (B0223.liftVec hε hc hP W)) w_hd) :
    ∫⁻ t in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (t ^ (-2 : ℝ)) *
          (∫⁻ p, ‖periodize c (W : Profile → MeridC) (Real.exp t * p.1, p.2) -
              periodize c (W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c)) ≤
      ENNReal.ofReal (10 * Real.exp 2 * ‖w_hd‖ ^ 2 + 2 * Real.exp 2 * ‖W‖ ^ 2) := by
  let b := periodize c (W : Profile → MeridC)
  have hb_meas : Measurable b := measurable_periodize_any c (Lp.stronglyMeasurable W).measurable
  have hpt_t : ∀ t ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (t ^ (-2 : ℝ)) *
          (∫⁻ p, ‖b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ) ∂(measureH c)) ≤
        ENNReal.ofReal (2 * Real.exp 2) *
          (ENNReal.ofReal (t ^ (-2 : ℝ)) *
            ‖FreeStress.phaseDilation P t (U (B0223.liftVec hε hc hP W)) -
              U (B0223.liftVec hε hc hP W)‖ₑ ^ (2 : ℝ)) +
        ENNReal.ofReal (2 * Real.exp 2 * ‖W‖ ^ 2) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hscale_m : Measurable fun p : Profile => (Real.exp t * p.1, p.2) :=
      (measurable_fst.const_mul (Real.exp t)).prodMk measurable_snd
    have hm_dil : Measurable fun p : Profile =>
        ‖(Real.exp (-(t / 4)) : ℂ) • b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ) :=
      (((hb_meas.comp hscale_m).const_smul ((Real.exp (-(t / 4)) : ℂ))).sub
        hb_meas).enorm.pow_const (2 : ℝ)
    have hm_b : Measurable fun p : Profile => ‖b p‖ₑ ^ (2 : ℝ) :=
      hb_meas.enorm.pow_const (2 : ℝ)
    have hp_le : ∫⁻ p, ‖b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ) ∂(measureH c) ≤
        ENNReal.ofReal (2 * Real.exp 2) *
          ‖FreeStress.phaseDilation P t (U (B0223.liftVec hε hc hP W)) -
            U (B0223.liftVec hε hc hP W)‖ₑ ^ (2 : ℝ) +
        ENNReal.ofReal (2 * Real.exp 2 * t ^ 2) * ENNReal.ofReal (‖W‖ ^ 2) := by
      calc ∫⁻ p, ‖b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ) ∂(measureH c)
          ≤ ∫⁻ p,
              (ENNReal.ofReal (2 * Real.exp 2) *
                ‖(Real.exp (-(t / 4)) : ℂ) • b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ) +
                ENNReal.ofReal (2 * Real.exp 2 * t ^ 2) * ‖b p‖ₑ ^ (2 : ℝ))
              ∂(measureH c) :=
            lintegral_mono fun p => exp_age_diff_enorm_sq_le ht _ _
        _ = ENNReal.ofReal (2 * Real.exp 2) *
              (∫⁻ p, ‖(Real.exp (-(t / 4)) : ℂ) • b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ)
                ∂(measureH c)) +
            ENNReal.ofReal (2 * Real.exp 2 * t ^ 2) *
              (∫⁻ p, ‖b p‖ₑ ^ (2 : ℝ) ∂(measureH c)) := by
            rw [lintegral_add_left (hm_dil.const_mul _),
              lintegral_const_mul _ hm_dil, lintegral_const_mul _ hm_b]
        _ = ENNReal.ofReal (2 * Real.exp 2) *
              ‖FreeStress.phaseDilation P t (U (B0223.liftVec hε hc hP W)) -
                U (B0223.liftVec hε hc hP W)‖ₑ ^ (2 : ℝ) +
            ENNReal.ofReal (2 * Real.exp 2 * t ^ 2) * ENNReal.ofReal (‖W‖ ^ 2) := by
            rw [lintegral_measureH_exp_age_sub_sq_eq hε hc hP U hU W t,
              lintegral_periodize_sq_eq_ofReal_norm_sq hc W]
    have hcancel : t ^ (-2 : ℝ) * (2 * Real.exp 2 * t ^ 2) = 2 * Real.exp 2 := by
      have h1 : t ^ (-2 : ℝ) * t ^ 2 = 1 := by
        rw [← Real.rpow_two, ← Real.rpow_add ht0]
        norm_num
      calc t ^ (-2 : ℝ) * (2 * Real.exp 2 * t ^ 2)
          = 2 * Real.exp 2 * (t ^ (-2 : ℝ) * t ^ 2) := by ring
        _ = 2 * Real.exp 2 := by rw [h1, mul_one]
    calc ENNReal.ofReal (t ^ (-2 : ℝ)) *
            (∫⁻ p, ‖b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ) ∂(measureH c))
        ≤ ENNReal.ofReal (t ^ (-2 : ℝ)) *
            (ENNReal.ofReal (2 * Real.exp 2) *
              ‖FreeStress.phaseDilation P t (U (B0223.liftVec hε hc hP W)) -
                U (B0223.liftVec hε hc hP W)‖ₑ ^ (2 : ℝ) +
            ENNReal.ofReal (2 * Real.exp 2 * t ^ 2) * ENNReal.ofReal (‖W‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hp_le zero_le
      _ = ENNReal.ofReal (2 * Real.exp 2) *
            (ENNReal.ofReal (t ^ (-2 : ℝ)) *
              ‖FreeStress.phaseDilation P t (U (B0223.liftVec hε hc hP W)) -
                U (B0223.liftVec hε hc hP W)‖ₑ ^ (2 : ℝ)) +
          ENNReal.ofReal (2 * Real.exp 2 * ‖W‖ ^ 2) := by
          rw [mul_add, ← mul_assoc, mul_comm (ENNReal.ofReal (t ^ (-2 : ℝ)))
              (ENNReal.ofReal (2 * Real.exp 2)), mul_assoc,
            ← mul_assoc (ENNReal.ofReal (t ^ (-2 : ℝ))),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), hcancel,
            ← ENNReal.ofReal_mul (by positivity)]
  have hmono : ∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (t ^ (-2 : ℝ)) *
        (∫⁻ p, ‖b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ) ∂(measureH c)) ≤
      ∫⁻ t in Ioo (0 : ℝ) 1,
        (ENNReal.ofReal (2 * Real.exp 2) *
          (ENNReal.ofReal (t ^ (-2 : ℝ)) *
            ‖FreeStress.phaseDilation P t (U (B0223.liftVec hε hc hP W)) -
              U (B0223.liftVec hε hc hP W)‖ₑ ^ (2 : ℝ)) +
          ENNReal.ofReal (2 * Real.exp 2 * ‖W‖ ^ 2)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hpt_t t ht
  refine hmono.trans ?_
  rw [lintegral_add_right _ measurable_const,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
  have hdil_le : ∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (t ^ (-2 : ℝ)) *
        ‖FreeStress.phaseDilation P t (U (B0223.liftVec hε hc hP W)) -
          U (B0223.liftVec hε hc hP W)‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (5 * ‖w_hd‖ ^ 2) :=
    (lintegral_mono_set Ioo_subset_Ioi_self).trans (lintegral_Ioi_phaseDilation_sub_sq_le hw)
  calc ENNReal.ofReal (2 * Real.exp 2) *
          (∫⁻ t in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (t ^ (-2 : ℝ)) *
              ‖FreeStress.phaseDilation P t (U (B0223.liftVec hε hc hP W)) -
                U (B0223.liftVec hε hc hP W)‖ₑ ^ (2 : ℝ)) +
        ENNReal.ofReal (2 * Real.exp 2 * ‖W‖ ^ 2)
      ≤ ENNReal.ofReal (2 * Real.exp 2) * ENNReal.ofReal (5 * ‖w_hd‖ ^ 2) +
          ENNReal.ofReal (2 * Real.exp 2 * ‖W‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hdil_le zero_le) (le_refl _)
    _ = ENNReal.ofReal (10 * Real.exp 2 * ‖w_hd‖ ^ 2 + 2 * Real.exp 2 * ‖W‖ ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-! ### 2. Step B: Slice `L²` difference `sliceDiffSq` and log-age Slobodeckij reduction -/

@[irreducible]
private def sliceDiffSq (c : ℝ) (b : Profile → MeridC) (s u : ℝ) : ℝ≥0∞ :=
  ∫⁻ q in Ioc 0 c, ∫⁻ η : ℝ, ‖b (s + u, q, η) - b (s, q, η)‖ₑ ^ (2 : ℝ)

private theorem measurable_uncurry_sliceDiffSq {c : ℝ} {b : Profile → MeridC} (hb : Measurable b) :
    Measurable (Function.uncurry (sliceDiffSq c b)) := by
  unfold sliceDiffSq
  have hm_shift : Measurable fun x : ((ℝ × ℝ) × ℝ) × ℝ =>
      (x.1.1.1 + x.1.1.2, x.1.2, x.2) :=
    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hm_base : Measurable fun x : ((ℝ × ℝ) × ℝ) × ℝ =>
      (x.1.1.1, x.1.2, x.2) :=
    ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hG₁ : Measurable fun x : ((ℝ × ℝ) × ℝ) × ℝ =>
      ‖b (x.1.1.1 + x.1.1.2, x.1.2, x.2) - b (x.1.1.1, x.1.2, x.2)‖ₑ ^ (2 : ℝ) :=
    ((hb.comp hm_shift).sub (hb.comp hm_base)).enorm.pow_const (2 : ℝ)
  exact (hG₁.lintegral_prod_right' (ν := (volume : Measure ℝ))).lintegral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioc 0 c))

private theorem lintegral_measureH_exp_slice_eq (c t : ℝ) {b : Profile → MeridC}
    (hb : Measurable b) :
    ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
          sliceDiffSq c b s ((Real.exp t - 1) * s) =
      ∫⁻ p, ‖b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
  let F : Profile → ℝ≥0∞ := fun p => ‖b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ)
  have hscale_m : Measurable fun p : Profile => (Real.exp t * p.1, p.2) :=
    (measurable_fst.const_mul (Real.exp t)).prodMk measurable_snd
  have hF_m : Measurable F := ((hb.comp hscale_m).sub hb).enorm.pow_const (2 : ℝ)
  have hmh : ∫⁻ p, F p ∂(measureH c) = ∫⁻ p, weightH p * F p ∂(cellMeasure c) := by
    rw [measureH, lintegral_withDensity_eq_lintegral_mul _ measurable_weightH hF_m]
    rfl
  rw [hmh, B0220.lintegral_cellMeasure c (fun p => weightH p * F p) (measurable_weightH.mul hF_m)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  unfold sliceDiffSq
  dsimp only [weightH, F]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioc fun q _ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun η => ?_
  have hs_eq : s + (Real.exp t - 1) * s = Real.exp t * s := by ring
  rw [hs_eq]

private theorem setLIntegral_Icc_Ioo_sliceDiffSq_le {c σ H1 δ : ℝ}
    (hσ : 0 < σ) (hσH : σ ≤ H1) (hδs : δ ≤ σ / 4)
    {b : Profile → MeridC} (hb : Measurable b) :
    ∫⁻ s in Icc (σ / 4) (H1 + 2),
        ∫⁻ u in Ioo 0 δ, ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u ≤
      ENNReal.ofReal (Real.exp 1 * (2 + H1)) *
        ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (t ^ (-2 : ℝ)) *
            (∫⁻ p, ‖b (Real.exp t * p.1, p.2) - b p‖ₑ ^ (2 : ℝ) ∂(measureH c)) := by
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hpt_s : ∀ s ∈ Icc (σ / 4) (H1 + 2),
      ∫⁻ u in Ioo 0 δ, ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u ≤
        ENNReal.ofReal (Real.exp 1 * (2 + H1)) *
          (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
            ∫⁻ t in Ioo (0 : ℝ) 1,
              ENNReal.ofReal (t ^ (-2 : ℝ)) *
                sliceDiffSq c b s ((Real.exp t - 1) * s)) := by
    intro s hs
    have hs_pos : 0 < s := lt_of_lt_of_le (by positivity : 0 < σ / 4) hs.1
    have hδ_le_s : δ ≤ s := hδs.trans hs.1
    have hcov := setLIntegral_Ioo_exp_sub_one_mul_le hs_pos hδ_le_s (sliceDiffSq c b s)
    have hs_inv_le : Real.exp 1 * s⁻¹ ≤ Real.exp 1 * (2 + H1) * s ^ (-(3 / 2 : ℝ)) := by
      have hs_le_2H1 : s ≤ 2 + H1 := by linarith [hs.2]
      have h1_le_2H1 : 1 ≤ 2 + H1 := by linarith
      have hrpow_half : s ^ (1 / 2 : ℝ) ≤ 2 + H1 := by
        calc s ^ (1 / 2 : ℝ)
            ≤ (2 + H1) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hs_pos.le hs_le_2H1 (by norm_num)
          _ ≤ (2 + H1) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1_le_2H1 (by norm_num)
          _ = 2 + H1 := Real.rpow_one _
      have hsinv_eq : s⁻¹ = s ^ (1 / 2 : ℝ) * s ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hs_pos, show (1 / 2 : ℝ) + (-(3 / 2 : ℝ)) = -1 by norm_num,
          Real.rpow_neg_one]
      rw [hsinv_eq]
      calc Real.exp 1 * (s ^ (1 / 2 : ℝ) * s ^ (-(3 / 2 : ℝ)))
          ≤ Real.exp 1 * ((2 + H1) * s ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hrpow_half (Real.rpow_nonneg hs_pos.le _))
              (Real.exp_pos 1).le
        _ = Real.exp 1 * (2 + H1) * s ^ (-(3 / 2 : ℝ)) := by ring
    refine hcov.trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hs_inv_le) zero_le
  have h1 : ∫⁻ s in Icc (σ / 4) (H1 + 2),
      ∫⁻ u in Ioo 0 δ, ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u ≤
      ENNReal.ofReal (Real.exp 1 * (2 + H1)) *
        ∫⁻ s in Ioi (0 : ℝ),
          ∫⁻ t in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
              (ENNReal.ofReal (t ^ (-2 : ℝ)) *
                sliceDiffSq c b s ((Real.exp t - 1) * s)) := by
    calc ∫⁻ s in Icc (σ / 4) (H1 + 2),
            ∫⁻ u in Ioo 0 δ, ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u
        ≤ ∫⁻ s in Icc (σ / 4) (H1 + 2),
            ENNReal.ofReal (Real.exp 1 * (2 + H1)) *
              (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
                ∫⁻ t in Ioo (0 : ℝ) 1,
                  ENNReal.ofReal (t ^ (-2 : ℝ)) *
                    sliceDiffSq c b s ((Real.exp t - 1) * s)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
          exact hpt_s s hs
      _ = ENNReal.ofReal (Real.exp 1 * (2 + H1)) *
            ∫⁻ s in Icc (σ / 4) (H1 + 2),
              ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
                ∫⁻ t in Ioo (0 : ℝ) 1,
                  ENNReal.ofReal (t ^ (-2 : ℝ)) *
                    sliceDiffSq c b s ((Real.exp t - 1) * s) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp 1 * (2 + H1)) *
            ∫⁻ s in Ioi (0 : ℝ),
              ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
                ∫⁻ t in Ioo (0 : ℝ) 1,
                  ENNReal.ofReal (t ^ (-2 : ℝ)) *
                    sliceDiffSq c b s ((Real.exp t - 1) * s) := by
          refine mul_le_mul_of_nonneg_left (lintegral_mono_set fun s hs => ?_) zero_le
          exact lt_of_lt_of_le (by positivity : 0 < σ / 4) hs.1
      _ = ENNReal.ofReal (Real.exp 1 * (2 + H1)) *
            ∫⁻ s in Ioi (0 : ℝ),
              ∫⁻ t in Ioo (0 : ℝ) 1,
                ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
                  (ENNReal.ofReal (t ^ (-2 : ℝ)) *
                    sliceDiffSq c b s ((Real.exp t - 1) * s)) := by
          congr 1
          refine lintegral_congr fun s => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine h1.trans (le_of_eq ?_)
  congr 1
  let G : ℝ → ℝ → ℝ≥0∞ := fun s t =>
    ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
      (ENNReal.ofReal (t ^ (-2 : ℝ)) *
        sliceDiffSq c b s ((Real.exp t - 1) * s))
  have hm_slice : Measurable fun st : ℝ × ℝ =>
      sliceDiffSq c b st.1 ((Real.exp st.2 - 1) * st.1) :=
    (measurable_uncurry_sliceDiffSq hb).comp
      (measurable_fst.prodMk
        (((Real.continuous_exp.measurable.comp measurable_snd).sub measurable_const).mul
          measurable_fst))
  have hm_prod : Measurable (Function.uncurry G) := by
    refine ((ENNReal.measurable_ofReal.comp
      (measurable_fst.pow_const (-(3 / 2 : ℝ))))).mul ?_
    exact (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const (-2 : ℝ))).mul hm_slice
  rw [lintegral_lintegral_swap (f := G) hm_prod.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  have hcomm : (fun s : ℝ =>
      ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
        (ENNReal.ofReal (t ^ (-2 : ℝ)) *
          sliceDiffSq c b s ((Real.exp t - 1) * s))) =
      fun s => ENNReal.ofReal (t ^ (-2 : ℝ)) *
        (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
          sliceDiffSq c b s ((Real.exp t - 1) * s)) := by
    funext s
    rw [← mul_assoc, mul_comm (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))), mul_assoc]
  rw [hcomm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_measureH_exp_slice_eq c t hb]

/-! ### 3. Step C: Averaged triangle inequality over `u ∈ Ioo 0 δ` -/

private theorem sliceDiffSq_triangle_le {c : ℝ} {b : Profile → MeridC} (hb : Measurable b)
    (s δ : ℝ) {u : ℝ} (hu : u ∈ Ioo 0 δ) :
    sliceDiffSq c b s δ ≤
      (2 * ENNReal.ofReal (δ ^ 2)) *
        (ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) * sliceDiffSq c b (s + u) (δ - u)) +
      (2 * ENNReal.ofReal (δ ^ 2)) *
        (ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u) := by
  have hu0 : 0 < u := hu.1
  have huδ : u < δ := hu.2
  have hδ_pos : 0 < δ := hu0.trans huδ
  have hsub_pos : 0 < δ - u := sub_pos.2 huδ
  have hm1_inner : ∀ q : ℝ, Measurable fun η : ℝ =>
      ‖b ((s + u) + (δ - u), q, η) - b (s + u, q, η)‖ₑ ^ (2 : ℝ) := fun q =>
    ((hb.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).sub
      (hb.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).enorm.pow_const _
  have hm1_q : Measurable fun q : ℝ =>
      ∫⁻ η : ℝ, ‖b ((s + u) + (δ - u), q, η) - b (s + u, q, η)‖ₑ ^ (2 : ℝ) := by
    have hm_pair : Measurable fun x : ℝ × ℝ =>
        ‖b ((s + u) + (δ - u), x.1, x.2) - b (s + u, x.1, x.2)‖ₑ ^ (2 : ℝ) :=
      ((hb.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).sub
        (hb.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))).enorm.pow_const _
    exact hm_pair.lintegral_prod_right'
  have hsplit_slice : sliceDiffSq c b s δ ≤
      2 * sliceDiffSq c b (s + u) (δ - u) + 2 * sliceDiffSq c b s u := by
    unfold sliceDiffSq
    have hq_le : ∀ q : ℝ,
        (∫⁻ η : ℝ, ‖b (s + δ, q, η) - b (s, q, η)‖ₑ ^ (2 : ℝ)) ≤
          2 * (∫⁻ η : ℝ, ‖b ((s + u) + (δ - u), q, η) - b (s + u, q, η)‖ₑ ^ (2 : ℝ)) +
          2 * (∫⁻ η : ℝ, ‖b (s + u, q, η) - b (s, q, η)‖ₑ ^ (2 : ℝ)) := by
      intro q
      calc ∫⁻ η : ℝ, ‖b (s + δ, q, η) - b (s, q, η)‖ₑ ^ (2 : ℝ)
          ≤ ∫⁻ η : ℝ,
              (2 * ‖b ((s + u) + (δ - u), q, η) - b (s + u, q, η)‖ₑ ^ (2 : ℝ) +
                2 * ‖b (s + u, q, η) - b (s, q, η)‖ₑ ^ (2 : ℝ)) := by
            refine lintegral_mono fun η => ?_
            have heq : b (s + δ, q, η) - b (s, q, η) =
                (b ((s + u) + (δ - u), q, η) - b (s + u, q, η)) +
                  (b (s + u, q, η) - b (s, q, η)) := by
              rw [show (s + u) + (δ - u) = s + δ by ring]
              abel
            rw [heq]
            exact two_term_enorm_sq_le _ _
        _ = 2 * (∫⁻ η : ℝ, ‖b ((s + u) + (δ - u), q, η) - b (s + u, q, η)‖ₑ ^ (2 : ℝ)) +
            2 * (∫⁻ η : ℝ, ‖b (s + u, q, η) - b (s, q, η)‖ₑ ^ (2 : ℝ)) := by
            rw [lintegral_add_left ((hm1_inner q).const_mul 2),
              lintegral_const_mul' 2 _ (by norm_num),
              lintegral_const_mul' 2 _ (by norm_num)]
    calc ∫⁻ q in Ioc 0 c, ∫⁻ η : ℝ, ‖b (s + δ, q, η) - b (s, q, η)‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ q in Ioc 0 c,
            (2 * (∫⁻ η : ℝ, ‖b ((s + u) + (δ - u), q, η) - b (s + u, q, η)‖ₑ ^ (2 : ℝ)) +
              2 * (∫⁻ η : ℝ, ‖b (s + u, q, η) - b (s, q, η)‖ₑ ^ (2 : ℝ))) :=
          lintegral_mono hq_le
      _ = 2 * (∫⁻ q in Ioc 0 c,
            ∫⁻ η : ℝ, ‖b ((s + u) + (δ - u), q, η) - b (s + u, q, η)‖ₑ ^ (2 : ℝ)) +
          2 * (∫⁻ q in Ioc 0 c,
            ∫⁻ η : ℝ, ‖b (s + u, q, η) - b (s, q, η)‖ₑ ^ (2 : ℝ)) := by
          rw [lintegral_add_left (hm1_q.const_mul 2),
            lintegral_const_mul' 2 _ (by norm_num),
            lintegral_const_mul' 2 _ (by norm_num)]
  have h1_u : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal (u ^ (-2 : ℝ)) := by
    have hr : δ ^ (-2 : ℝ) ≤ u ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hu0 huδ.le (by norm_num)
    have hmul : 1 ≤ δ ^ 2 * u ^ (-2 : ℝ) := by
      calc (1 : ℝ)
          = δ ^ (2 : ℝ) * δ ^ (-2 : ℝ) := by rw [← Real.rpow_add hδ_pos]; norm_num
        _ = δ ^ 2 * δ ^ (-2 : ℝ) := by rw [Real.rpow_two]
        _ ≤ δ ^ 2 * u ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hr (sq_nonneg δ)
    rw [← ENNReal.ofReal_mul (sq_nonneg δ), ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hmul
  have h1_sub : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) := by
    have hr : δ ^ (-2 : ℝ) ≤ (δ - u) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hsub_pos (by linarith) (by norm_num)
    have hmul : 1 ≤ δ ^ 2 * (δ - u) ^ (-2 : ℝ) := by
      calc (1 : ℝ)
          = δ ^ (2 : ℝ) * δ ^ (-2 : ℝ) := by rw [← Real.rpow_add hδ_pos]; norm_num
        _ = δ ^ 2 * δ ^ (-2 : ℝ) := by rw [Real.rpow_two]
        _ ≤ δ ^ 2 * (δ - u) ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hr (sq_nonneg δ)
    rw [← ENNReal.ofReal_mul (sq_nonneg δ), ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hmul
  refine hsplit_slice.trans (add_le_add ?_ ?_)
  · calc 2 * sliceDiffSq c b (s + u) (δ - u)
        = 2 * (1 * sliceDiffSq c b (s + u) (δ - u)) := by rw [one_mul]
      _ ≤ 2 * ((ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal ((δ - u) ^ (-2 : ℝ))) *
            sliceDiffSq c b (s + u) (δ - u)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1_sub zero_le) zero_le
      _ = (2 * ENNReal.ofReal (δ ^ 2)) *
            (ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) * sliceDiffSq c b (s + u) (δ - u)) := by
          rw [← mul_assoc, ← mul_assoc, mul_assoc (2 * ENNReal.ofReal (δ ^ 2))]
  · calc 2 * sliceDiffSq c b s u
        = 2 * (1 * sliceDiffSq c b s u) := by rw [one_mul]
      _ ≤ 2 * ((ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal (u ^ (-2 : ℝ))) *
            sliceDiffSq c b s u) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1_u zero_le) zero_le
      _ = (2 * ENNReal.ofReal (δ ^ 2)) *
            (ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u) := by
          rw [← mul_assoc, ← mul_assoc, mul_assoc (2 * ENNReal.ofReal (δ ^ 2))]

private theorem setLIntegral_age_pos_shift_le {c σ H1 δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {b : Profile → MeridC} (hb : Measurable b) :
    ∫⁻ s in Icc (σ / 4) (H1 + 1), sliceDiffSq c b s δ ≤
      4 * ENNReal.ofReal δ *
        ∫⁻ s in Icc (σ / 4) (H1 + 2),
          ∫⁻ u in Ioo 0 δ, ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u := by
  have hm_un := measurable_uncurry_sliceDiffSq (c := c) hb
  let G₂ : ℝ → ℝ → ℝ≥0∞ := fun s u =>
    ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u
  let G₁ : ℝ → ℝ → ℝ≥0∞ := fun s u =>
    ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) * sliceDiffSq c b (s + u) (δ - u)
  have hm_su2 : Measurable (Function.uncurry G₂) :=
    (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const (-2 : ℝ))).mul hm_un
  have hm_su1 : Measurable (Function.uncurry G₁) :=
    (ENNReal.measurable_ofReal.comp
      ((measurable_const.sub measurable_snd).pow_const (-2 : ℝ))).mul
      (hm_un.comp ((measurable_fst.add measurable_snd).prodMk
        (measurable_const.sub measurable_snd)))
  have h2δ_ne_top : (2 : ℝ≥0∞) * ENNReal.ofReal (δ ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hpt_s : ∀ s : ℝ,
      ENNReal.ofReal δ * sliceDiffSq c b s δ ≤
        (2 * ENNReal.ofReal (δ ^ 2)) *
          (∫⁻ u in Ioo 0 δ,
            ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) * sliceDiffSq c b (s + u) (δ - u)) +
        (2 * ENNReal.ofReal (δ ^ 2)) *
          (∫⁻ u in Ioo 0 δ,
            ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u) := by
    intro s
    have hconst : ENNReal.ofReal δ * sliceDiffSq c b s δ =
        ∫⁻ _u in Ioo 0 δ, sliceDiffSq c b s δ := by
      rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]
    rw [hconst]
    have hm_u2 : Measurable fun u : ℝ =>
        (2 * ENNReal.ofReal (δ ^ 2)) *
          (ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u) :=
      (hm_su2.comp (measurable_const.prodMk measurable_id)).const_mul _
    calc ∫⁻ _u in Ioo 0 δ, sliceDiffSq c b s δ
        ≤ ∫⁻ u in Ioo 0 δ,
            ((2 * ENNReal.ofReal (δ ^ 2)) *
              (ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) * sliceDiffSq c b (s + u) (δ - u)) +
            (2 * ENNReal.ofReal (δ ^ 2)) *
              (ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
          exact sliceDiffSq_triangle_le hb s δ hu
      _ = (2 * ENNReal.ofReal (δ ^ 2)) *
            (∫⁻ u in Ioo 0 δ,
              ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) * sliceDiffSq c b (s + u) (δ - u)) +
          (2 * ENNReal.ofReal (δ ^ 2)) *
            (∫⁻ u in Ioo 0 δ,
              ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u) := by
          rw [lintegral_add_right _ hm_u2,
            lintegral_const_mul' _ _ h2δ_ne_top,
            lintegral_const_mul' _ _ h2δ_ne_top]
  have hm_s2 : Measurable fun s : ℝ =>
      (2 * ENNReal.ofReal (δ ^ 2)) *
        (∫⁻ u in Ioo 0 δ, ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u) :=
    (hm_su2.lintegral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioo 0 δ))).const_mul _
  have hint_s : ENNReal.ofReal δ * ∫⁻ s in Icc (σ / 4) (H1 + 1), sliceDiffSq c b s δ ≤
      (2 * ENNReal.ofReal (δ ^ 2)) *
        (∫⁻ s in Icc (σ / 4) (H1 + 1),
          ∫⁻ u in Ioo 0 δ,
            ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) * sliceDiffSq c b (s + u) (δ - u)) +
      (2 * ENNReal.ofReal (δ ^ 2)) *
        (∫⁻ s in Icc (σ / 4) (H1 + 1),
          ∫⁻ u in Ioo 0 δ,
            ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (lintegral_mono hpt_s).trans (le_of_eq ?_)
    rw [lintegral_add_right _ hm_s2,
      lintegral_const_mul' _ _ h2δ_ne_top,
      lintegral_const_mul' _ _ h2δ_ne_top]
  have hterm1_le :
      (∫⁻ s in Icc (σ / 4) (H1 + 1),
        ∫⁻ u in Ioo 0 δ,
          ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) * sliceDiffSq c b (s + u) (δ - u)) ≤
      ∫⁻ s in Icc (σ / 4) (H1 + 2),
        ∫⁻ u in Ioo 0 δ,
          ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u := by
    rw [lintegral_lintegral_swap (f := G₁) hm_su1.aemeasurable]
    have hshift_u :
        (∫⁻ u in Ioo 0 δ,
          ∫⁻ s in Icc (σ / 4) (H1 + 1),
            ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) * sliceDiffSq c b (s + u) (δ - u)) ≤
        ∫⁻ u in Ioo 0 δ,
          ∫⁻ s in Icc (σ / 4) (H1 + 2),
            ENNReal.ofReal ((δ - u) ^ (-2 : ℝ)) * sliceDiffSq c b s (δ - u) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hu0 : 0 < u := hu.1
      have hu1 : u ≤ 1 := hu.2.le.trans hδ1
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul_of_nonneg_left
        (setLIntegral_Icc_add_right_le u (by linarith) (by linarith)
          (fun s' => sliceDiffSq c b s' (δ - u)))
        zero_le
    refine hshift_u.trans (le_of_eq ?_)
    rw [setLIntegral_Ioo_sub_left_eq
      (fun v => ∫⁻ s in Icc (σ / 4) (H1 + 2),
        ENNReal.ofReal (v ^ (-2 : ℝ)) * sliceDiffSq c b s v)]
    exact (lintegral_lintegral_swap (f := G₂) hm_su2.aemeasurable).symm
  have hterm2_le :
      (∫⁻ s in Icc (σ / 4) (H1 + 1),
        ∫⁻ u in Ioo 0 δ,
          ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u) ≤
      ∫⁻ s in Icc (σ / 4) (H1 + 2),
        ∫⁻ u in Ioo 0 δ,
          ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u :=
    lintegral_mono_set (Icc_subset_Icc_right (by linarith))
  refine (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_pos.2 hδ0).ne' ENNReal.ofReal_ne_top).1 ?_
  set J : ℝ≥0∞ := ∫⁻ s in Icc (σ / 4) (H1 + 2),
      ∫⁻ u in Ioo 0 δ, ENNReal.ofReal (u ^ (-2 : ℝ)) * sliceDiffSq c b s u
  calc ENNReal.ofReal δ * ∫⁻ s in Icc (σ / 4) (H1 + 1), sliceDiffSq c b s δ
      ≤ (2 * ENNReal.ofReal (δ ^ 2)) * J + (2 * ENNReal.ofReal (δ ^ 2)) * J :=
        hint_s.trans
          (add_le_add
            (mul_le_mul_of_nonneg_left hterm1_le zero_le)
            (mul_le_mul_of_nonneg_left hterm2_le zero_le))
    _ = ENNReal.ofReal δ * (4 * ENNReal.ofReal δ * J) := by
        rw [sq δ, ENNReal.ofReal_mul hδ0.le]
        ring

/-! ### 4. Step D: Cutoff localisation, sign-of-`h` reduction, and scalar consolidations -/

private theorem lintegral_cutoff_shiftS_smul_le_sliceDiffSq {c σ H1 L1 h : ℝ}
    (hc : 0 < c) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    (hh_σ : |h| ≤ σ / 4) (hh_1 : |h| ≤ 1)
    {b : Profile → MeridC} (hb : Measurable b) :
    ∫⁻ p, ‖χ (shiftS h p) • (b (shiftS h p) - b p)‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (cNorm8 χ ^ 2) * ∫⁻ s in Icc (σ / 2) (H1 + 1), sliceDiffSq c b s h := by
  let F : Profile → ℝ≥0∞ := fun p =>
    (Icc (σ / 2) (H1 + 1)).indicator (fun _ => ENNReal.ofReal (cNorm8 χ ^ 2)) p.1 *
      ‖b (shiftS h p) - b p‖ₑ ^ (2 : ℝ)
  have hm_ind : Measurable
      ((Icc (σ / 2) (H1 + 1)).indicator (fun _ : ℝ => ENNReal.ofReal (cNorm8 χ ^ 2))) :=
    measurable_const.indicator measurableSet_Icc
  have hF_m : Measurable F :=
    (hm_ind.comp measurable_fst).mul
      (((hb.comp (measurable_shiftS h)).sub hb).enorm.pow_const (2 : ℝ))
  have hpt : ∀ p : Profile,
      ‖χ (shiftS h p) • (b (shiftS h p) - b p)‖ₑ ^ (2 : ℝ) ≤ F p := by
    intro p
    by_cases hp0 : χ (shiftS h p) = 0
    · simp [hp0]
    · obtain ⟨hs1, hs2, _⟩ := hχ.support (shiftS h p) hp0
      change σ ≤ p.1 + h at hs1
      change p.1 + h ≤ H1 at hs2
      obtain ⟨hhl, hhu⟩ := abs_le.1 hh_σ
      obtain ⟨hhl1, _⟩ := abs_le.1 hh_1
      have hp_mem : p.1 ∈ Icc (σ / 2) (H1 + 1) := ⟨by linarith, by linarith⟩
      have hbd := abs_le_cNorm8_of_nearCutoff hc hχ (shiftS h p)
      have hnorm : ‖χ (shiftS h p) • (b (shiftS h p) - b p)‖ ≤
          cNorm8 χ * ‖b (shiftS h p) - b p‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hbd (norm_nonneg _)
      have hsq : ‖χ (shiftS h p) • (b (shiftS h p) - b p)‖ ^ 2 ≤
          cNorm8 χ ^ 2 * ‖b (shiftS h p) - b p‖ ^ 2 := by
        calc ‖χ (shiftS h p) • (b (shiftS h p) - b p)‖ ^ 2
            ≤ (cNorm8 χ * ‖b (shiftS h p) - b p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
          _ = cNorm8 χ ^ 2 * ‖b (shiftS h p) - b p‖ ^ 2 := mul_pow _ _ 2
      dsimp only [F]
      rw [indicator_of_mem hp_mem, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two,
        ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two,
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hsq
  calc ∫⁻ p, ‖χ (shiftS h p) • (b (shiftS h p) - b p)‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ∫⁻ p, F p ∂(cellMeasure c) := lintegral_mono hpt
    _ = ∫⁻ s in Ioi (0 : ℝ),
          (Icc (σ / 2) (H1 + 1)).indicator
            (fun s' => ENNReal.ofReal (cNorm8 χ ^ 2) * sliceDiffSq c b s' h) s := by
        rw [B0220.lintegral_cellMeasure c F hF_m]
        refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        by_cases hs : s ∈ Icc (σ / 2) (H1 + 1)
        · unfold sliceDiffSq
          simp only [F, indicator_of_mem hs, shiftS]
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine setLIntegral_congr_fun measurableSet_Ioc fun q _ => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        · simp [F, indicator_of_notMem hs]
    _ ≤ ∫⁻ s : ℝ,
          (Icc (σ / 2) (H1 + 1)).indicator
            (fun s' => ENNReal.ofReal (cNorm8 χ ^ 2) * sliceDiffSq c b s' h) s :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (cNorm8 χ ^ 2) * ∫⁻ s in Icc (σ / 2) (H1 + 1), sliceDiffSq c b s h := by
        rw [lintegral_indicator measurableSet_Icc,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem setLIntegral_sliceDiffSq_abs_le {c σ H1 h : ℝ}
    (hσ : 0 < σ) (hh_ne : h ≠ 0) (hh_σ : |h| ≤ σ / 4) (b : Profile → MeridC) :
    ∫⁻ s in Icc (σ / 2) (H1 + 1), sliceDiffSq c b s h ≤
      ∫⁻ s in Icc (σ / 4) (H1 + 1), sliceDiffSq c b s |h| := by
  rcases lt_trichotomy h 0 with hneg | rfl | hpos
  · have habs : |h| = -h := abs_of_neg hneg
    have hrev : ∀ s : ℝ, sliceDiffSq c b s h = sliceDiffSq c b (s + h) |h| := fun s => by
      unfold sliceDiffSq
      refine setLIntegral_congr_fun measurableSet_Ioc fun q _ => ?_
      refine lintegral_congr fun η => ?_
      rw [habs, show (s + h) + -h = s by ring, ← ofReal_norm, ← ofReal_norm,
        norm_sub_rev (b (s + h, q, η))]
    have hcongr : ∫⁻ s in Icc (σ / 2) (H1 + 1), sliceDiffSq c b s h =
        ∫⁻ s in Icc (σ / 2) (H1 + 1), sliceDiffSq c b (s + h) |h| :=
      setLIntegral_congr_fun measurableSet_Icc fun s _ => hrev s
    rw [hcongr]
    obtain ⟨hhl, _⟩ := abs_le.1 hh_σ
    exact setLIntegral_Icc_add_right_le h (by linarith) (by linarith)
      (fun s' => sliceDiffSq c b s' |h|)
  · exact (hh_ne rfl).elim
  · rw [abs_of_pos hpos]
    exact lintegral_mono_set (Icc_subset_Icc_left (by linarith))

/-- Scalar consolidation for large shifts `min (1 / 4) (σ / 4) ≤ |h|`. -/
private theorem shiftS_large_scalar_consolidation {Gam H1 σ cN nW N_W h : ℝ}
    (hG1 : 1 ≤ Gam) (hσ : 0 < σ) (hσH : σ ≤ H1)
    (h1H1 : 1 + H1 ≤ Gam) (h1σ : 1 + σ⁻¹ ≤ Gam)
    (hcN0 : 0 ≤ cN) (hcN : cN ≤ Gam)
    (hnW0 : 0 ≤ nW) (hnW : nW ≤ N_W) (_hNW0 : 0 ≤ N_W)
    (hh_large : min (1 / 4 : ℝ) (σ / 4) ≤ |h|) :
    ENNReal.ofReal ((2 * ((1 + H1) * cN * nW)) ^ 2) ≤
      ENNReal.ofReal ((10 * Real.exp 2 * Gam ^ 3 * N_W) ^ 2 * |h|) := by
  refine ENNReal.ofReal_le_ofReal ?_
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have h1_le_min : 1 ≤ 4 * (1 + σ⁻¹) * min (1 / 4 : ℝ) (σ / 4) := by
    rcases min_cases (1 / 4 : ℝ) (σ / 4) with ⟨hmin, _⟩ | ⟨hmin, _⟩
    · rw [hmin]
      have : 0 < σ⁻¹ := inv_pos.2 hσ
      linarith
    · rw [hmin]
      have h1 : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ.ne'
      linarith
  have h1_le_Gam_h : 1 ≤ 4 * Gam ^ 2 * |h| := by
    have hG_G2 : Gam ≤ Gam ^ 2 := by nlinarith
    calc (1 : ℝ)
        ≤ 4 * (1 + σ⁻¹) * min (1 / 4 : ℝ) (σ / 4) := h1_le_min
      _ ≤ 4 * (1 + σ⁻¹) * |h| :=
          mul_le_mul_of_nonneg_left hh_large (by positivity)
      _ ≤ 4 * Gam * |h| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1σ (by norm_num)) (abs_nonneg h)
      _ ≤ 4 * Gam ^ 2 * |h| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG_G2 (by norm_num)) (abs_nonneg h)
  have hprod : (1 + H1) * cN * nW ≤ Gam ^ 2 * N_W := by
    have hcut : (1 + H1) * cN ≤ Gam ^ 2 := by
      calc (1 + H1) * cN ≤ Gam * Gam := mul_le_mul h1H1 hcN hcN0 hG0
        _ = Gam ^ 2 := (sq Gam).symm
    exact mul_le_mul hcut hnW hnW0 (sq_nonneg Gam)
  have h0_l : 0 ≤ 2 * ((1 + H1) * cN * nW) :=
    mul_nonneg zero_le_two (mul_nonneg (mul_nonneg (by linarith) hcN0) hnW0)
  have hsq : (2 * ((1 + H1) * cN * nW)) ^ 2 ≤ 4 * Gam ^ 4 * N_W ^ 2 := by
    have h2 : 2 * ((1 + H1) * cN * nW) ≤ 2 * (Gam ^ 2 * N_W) :=
      mul_le_mul_of_nonneg_left hprod zero_le_two
    calc (2 * ((1 + H1) * cN * nW)) ^ 2
        ≤ (2 * (Gam ^ 2 * N_W)) ^ 2 := pow_le_pow_left₀ h0_l h2 2
      _ = 4 * Gam ^ 4 * N_W ^ 2 := by ring
  have hexp1 : 1 ≤ Real.exp 2 ^ 2 := one_le_pow₀ (Real.one_le_exp (by norm_num))
  calc (2 * ((1 + H1) * cN * nW)) ^ 2
      ≤ 4 * Gam ^ 4 * N_W ^ 2 * 1 := by linarith
    _ ≤ 4 * Gam ^ 4 * N_W ^ 2 * (4 * Gam ^ 2 * |h|) :=
        mul_le_mul_of_nonneg_left h1_le_Gam_h (by positivity)
    _ = 16 * 1 * (Gam ^ 6 * N_W ^ 2 * |h|) := by ring
    _ ≤ 100 * Real.exp 2 ^ 2 * (Gam ^ 6 * N_W ^ 2 * |h|) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith
    _ = (10 * Real.exp 2 * Gam ^ 3 * N_W) ^ 2 * |h| := by ring

/-- Scalar consolidation for small shifts `0 < |h| ≤ 1`. -/
private theorem shiftS_small_scalar_consolidation {Gam H1 cN nW nwhd N_W h : ℝ}
    (hG1 : 1 ≤ Gam) (hH1_pos : 0 < H1)
    (h2H1 : 2 + H1 ≤ Gam) (hcN0 : 0 ≤ cN) (hcN : cN ≤ Gam)
    (hnW0 : 0 ≤ nW) (hnW : nW ≤ N_W)
    (hnwhd0 : 0 ≤ nwhd) (hnwhd : nwhd ≤ N_W)
    (_hNW0 : 0 ≤ N_W) (hh1 : |h| ≤ 1) :
    2 * (ENNReal.ofReal (cN ^ 2) *
          (4 * ENNReal.ofReal |h| *
            (ENNReal.ofReal (Real.exp 1 * (2 + H1)) *
              ENNReal.ofReal (10 * Real.exp 2 * nwhd ^ 2 + 2 * Real.exp 2 * nW ^ 2)))) +
      2 * ENNReal.ofReal (((1 + (H1 + 1)) * (cN * |h|) * nW) ^ 2) ≤
      ENNReal.ofReal ((10 * Real.exp 2 * Gam ^ 3 * N_W) ^ 2 * |h|) := by
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hh_sq : |h| ^ 2 ≤ |h| := by
    calc |h| ^ 2 = |h| * |h| := sq |h|
      _ ≤ 1 * |h| := mul_le_mul_of_nonneg_right hh1 (abs_nonneg h)
      _ = |h| := one_mul |h|
  have hofReal_num : ∀ (k : ℝ) (x : ℝ), 0 ≤ k → 0 ≤ x →
      ENNReal.ofReal k * ENNReal.ofReal x = ENNReal.ofReal (k * x) :=
    fun k x hk _ => (ENNReal.ofReal_mul hk).symm
  have h2_eq : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  have h4_eq : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by norm_num
  have hterm1_eq :
      2 * (ENNReal.ofReal (cN ^ 2) *
          (4 * ENNReal.ofReal |h| *
            (ENNReal.ofReal (Real.exp 1 * (2 + H1)) *
              ENNReal.ofReal (10 * Real.exp 2 * nwhd ^ 2 + 2 * Real.exp 2 * nW ^ 2)))) =
      ENNReal.ofReal
        (8 * cN ^ 2 * |h| * (Real.exp 1 * (2 + H1)) *
          (10 * Real.exp 2 * nwhd ^ 2 + 2 * Real.exp 2 * nW ^ 2)) := by
    rw [h2_eq, h4_eq,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp 1 * (2 + H1)),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * |h|),
      ← ENNReal.ofReal_mul (sq_nonneg cN),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hterm2_eq :
      2 * ENNReal.ofReal (((1 + (H1 + 1)) * (cN * |h|) * nW) ^ 2) =
      ENNReal.ofReal (2 * ((2 + H1) * cN * nW) ^ 2 * |h| ^ 2) := by
    rw [h2_eq, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hterm1_eq, hterm2_eq, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hdil_NW : 10 * Real.exp 2 * nwhd ^ 2 + 2 * Real.exp 2 * nW ^ 2 ≤
      12 * Real.exp 2 * N_W ^ 2 := by
    have h1 : nwhd ^ 2 ≤ N_W ^ 2 := pow_le_pow_left₀ hnwhd0 hnwhd 2
    have h2 : nW ^ 2 ≤ N_W ^ 2 := pow_le_pow_left₀ hnW0 hnW 2
    have he2 : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
    nlinarith
  have hcN_G3 : cN ^ 2 * (2 + H1) ≤ Gam ^ 6 := by
    have hcN_sq : cN ^ 2 ≤ Gam ^ 2 := pow_le_pow_left₀ hcN0 hcN 2
    have hG3_G6 : Gam ^ 3 ≤ Gam ^ 6 := pow_le_pow_right₀ hG1 (by norm_num)
    calc cN ^ 2 * (2 + H1)
        ≤ Gam ^ 2 * Gam := mul_le_mul hcN_sq h2H1 (by positivity) (sq_nonneg Gam)
      _ = Gam ^ 3 := by ring
      _ ≤ Gam ^ 6 := hG3_G6
  have hexp3_4 : Real.exp 1 * Real.exp 2 ≤ Real.exp 2 ^ 2 := by
    rw [← Real.exp_add, sq, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by norm_num)
  have hb1 : 8 * cN ^ 2 * |h| * (Real.exp 1 * (2 + H1)) *
        (10 * Real.exp 2 * nwhd ^ 2 + 2 * Real.exp 2 * nW ^ 2) ≤
      96 * Real.exp 2 ^ 2 * Gam ^ 6 * N_W ^ 2 * |h| := by
    calc 8 * cN ^ 2 * |h| * (Real.exp 1 * (2 + H1)) *
            (10 * Real.exp 2 * nwhd ^ 2 + 2 * Real.exp 2 * nW ^ 2)
        ≤ 8 * cN ^ 2 * |h| * (Real.exp 1 * (2 + H1)) * (12 * Real.exp 2 * N_W ^ 2) :=
          mul_le_mul_of_nonneg_left hdil_NW (by positivity)
      _ = 96 * ((Real.exp 1 * Real.exp 2) * (cN ^ 2 * (2 + H1))) * (N_W ^ 2 * |h|) := by ring
      _ ≤ 96 * (Real.exp 2 ^ 2 * Gam ^ 6) * (N_W ^ 2 * |h|) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul hexp3_4 hcN_G3 (by positivity) (sq_nonneg _)
      _ = 96 * Real.exp 2 ^ 2 * Gam ^ 6 * N_W ^ 2 * |h| := by ring
  have hb2 : 2 * ((2 + H1) * cN * nW) ^ 2 * |h| ^ 2 ≤
      2 * Real.exp 2 ^ 2 * Gam ^ 6 * N_W ^ 2 * |h| := by
    have hprod : (2 + H1) * cN * nW ≤ Gam ^ 3 * N_W := by
      have h1 : (2 + H1) * cN ≤ Gam ^ 2 := by
        calc (2 + H1) * cN ≤ Gam * Gam := mul_le_mul h2H1 hcN hcN0 hG0
          _ = Gam ^ 2 := (sq Gam).symm
      have hG2_G3 : Gam ^ 2 ≤ Gam ^ 3 := pow_le_pow_right₀ hG1 (by norm_num)
      exact mul_le_mul (h1.trans hG2_G3) hnW hnW0 (pow_nonneg hG0 3)
    have hsq : ((2 + H1) * cN * nW) ^ 2 ≤ (Gam ^ 3 * N_W) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hprod 2
    have hexp1 : 1 ≤ Real.exp 2 ^ 2 := one_le_pow₀ (Real.one_le_exp (by norm_num))
    calc 2 * ((2 + H1) * cN * nW) ^ 2 * |h| ^ 2
        ≤ 2 * (Gam ^ 3 * N_W) ^ 2 * |h| :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq zero_le_two) hh_sq
            (sq_nonneg |h|) (by positivity)
      _ = 2 * 1 * (Gam ^ 6 * N_W ^ 2 * |h|) := by ring
      _ ≤ 2 * Real.exp 2 ^ 2 * (Gam ^ 6 * N_W ^ 2 * |h|) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith
      _ = 2 * Real.exp 2 ^ 2 * Gam ^ 6 * N_W ^ 2 * |h| := by ring
  have hnn : 0 ≤ Real.exp 2 ^ 2 * Gam ^ 6 * N_W ^ 2 * |h| := by positivity
  calc 8 * cN ^ 2 * |h| * (Real.exp 1 * (2 + H1)) *
          (10 * Real.exp 2 * nwhd ^ 2 + 2 * Real.exp 2 * nW ^ 2) +
        2 * ((2 + H1) * cN * nW) ^ 2 * |h| ^ 2
      ≤ 96 * Real.exp 2 ^ 2 * Gam ^ 6 * N_W ^ 2 * |h| +
          2 * Real.exp 2 ^ 2 * Gam ^ 6 * N_W ^ 2 * |h| := add_le_add hb1 hb2
    _ ≤ 100 * Real.exp 2 ^ 2 * Gam ^ 6 * N_W ^ 2 * |h| := by nlinarith
    _ = (10 * Real.exp 2 * Gam ^ 3 * N_W) ^ 2 * |h| := by ring

/-- Proof of the age (`shiftS`) chart-pullback and cutoff-localisation leaf
`PhaseHalfDriftCutoffShiftS` (`PartII-a:N05/3/1/1`). -/
theorem phaseHalfDriftCutoffShiftS : PhaseHalfDriftCutoffShiftS := by
  refine ⟨3, 10 * Real.exp 2, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM hχ _hχ1 hm _B _hB ε hε _hε1 P _ hP _hP1
    U hU W w_hd g_diss hw _hg h hh
  have hG1 := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hW_norm : ‖W‖ = ‖U (B0223.liftVec hε hc hP W)‖ :=
    (norm_phaseLift_liftVec hε hc hP U W).symm
  have hsum_nn : 0 ≤ ∑ j : Fin 3, ‖g_diss j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hW_le_NW : ‖W‖ ≤ ‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ := by
    rw [hW_norm]
    exact (le_add_of_nonneg_right (norm_nonneg w_hd)).trans (le_add_of_nonneg_right hsum_nn)
  have hwhd_le_NW :
      ‖w_hd‖ ≤ ‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ :=
    (le_add_of_nonneg_left (norm_nonneg (U (B0223.liftVec hε hc hP W)))).trans
      (le_add_of_nonneg_right hsum_nn)
  have hNW0 : 0 ≤ ‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ :=
    (norm_nonneg W).trans hW_le_NW
  have hh1 : |h| ≤ 1 := abs_le.2 ⟨hh.1, hh.2⟩
  have hR0 : 0 ≤
      (10 * Real.exp 2 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 *
        (‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖)) ^ 2 * |h| :=
    mul_nonneg (sq_nonneg _) (abs_nonneg h)
  by_cases hh0 : h = 0
  · subst hh0
    have hzero : (fun p : Profile =>
        ‖flatStressCutRep c χ W (shiftS 0 p) - flatStressCutRep c χ W p‖ ^ 2) = fun _ => 0 := by
      funext p
      have hsh0 : shiftS 0 p = p := by
        rcases p with ⟨s, q, η⟩
        simp [shiftS]
      simp [hsh0]
    rw [hzero, integral_zero]
    exact hR0
  · have hf_meas : Measurable
        (fun p => flatStressCutRep c χ W (shiftS h p) - flatStressCutRep c χ W p) :=
      ((measurable_flatStressCutRep c hm W).comp (measurable_shiftS h)).sub
        (measurable_flatStressCutRep c hm W)
    refine integral_norm_sq_le_of_lintegral_le hf_meas hR0 ?_
    by_cases hh_large : min (1 / 4 : ℝ) (σ / 4) ≤ |h|
    · have huniv := lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm
        (measurable_shiftS h) (fun f hf _ hsupp => lintegral_shiftS_le c h hf hsupp) W
      exact huniv.trans
        (shiftS_large_scalar_consolidation hG1 hσ hσH
          (one_add_H1_le_gamma χ χ1 hν hc hσ hL1 hγ hM)
          (one_add_inv_sigma_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM)
          (cNorm8_nonneg χ)
          (cNorm8_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM)
          (norm_nonneg W) hW_le_NW hNW0 hh_large)
    · have hh_lt : |h| < min (1 / 4 : ℝ) (σ / 4) := lt_of_not_ge hh_large
      have hh_pos : 0 < |h| := abs_pos.2 hh0
      have hh_14 : |h| ≤ 1 / 4 := hh_lt.le.trans (min_le_left _ _)
      have hh_σ4 : |h| ≤ σ / 4 := hh_lt.le.trans (min_le_right _ _)
      have hsplit := lintegral_flatStressCutRep_shift_sub_sq_le_split hm (measurable_shiftS h) W
      let ψ : Profile → ℝ := fun q => χ (shiftS h q) - χ q
      have hψ_m : Measurable ψ := (hm.comp (measurable_shiftS h)).sub hm
      have hψ_bd : ∀ q, |ψ q| ≤ cNorm8 χ * |h| := fun q => by
        calc |χ (shiftS h q) - χ q|
            ≤ cNorm8 χ * ‖shiftS h q - q‖ := abs_cutoff_sub_le hc hχ q (shiftS h q)
          _ = cNorm8 χ * |h| := by rw [norm_shiftS_sub]
      have hψ_supp : ∀ q, ψ q ≠ 0 → σ / 2 ≤ q.1 ∧ q.1 ≤ H1 + 1 := fun q hq => by
        obtain ⟨hhl, hhu⟩ := abs_le.1 hh_σ4
        obtain ⟨hhl1, _⟩ := abs_le.1 hh1
        by_cases h1 : χ (shiftS h q) = 0
        · have h2 : χ q ≠ 0 := fun h0 => hq (by simp [ψ, h1, h0])
          obtain ⟨hs1, hs2, _⟩ := hχ.support q h2
          exact ⟨by linarith, by linarith⟩
        · obtain ⟨hs1, hs2, _⟩ := hχ.support (shiftS h q) h1
          change σ ≤ q.1 + h at hs1
          change q.1 + h ≤ H1 at hs2
          exact ⟨by linarith, by linarith⟩
      have hI₂ := lintegral_bounded_smul_periodize_sq_le hc (by positivity : 0 < σ / 2)
        (by linarith : σ / 2 ≤ H1 + 1) hψ_m hψ_bd hψ_supp W
      have hb_meas : Measurable (periodize c (W : Profile → MeridC)) :=
        measurable_periodize_any c (Lp.stronglyMeasurable W).measurable
      have hI₁_a := lintegral_cutoff_shiftS_smul_le_sliceDiffSq hc hχ hh_σ4 hh1 hb_meas
      have hI₁_b := setLIntegral_sliceDiffSq_abs_le (c := c) (H1 := H1) hσ hh0 hh_σ4
        (periodize c (W : Profile → MeridC))
      have hstepC := setLIntegral_age_pos_shift_le (c := c) (σ := σ) (H1 := H1) hh_pos hh1 hb_meas
      have hstepB := setLIntegral_Icc_Ioo_sliceDiffSq_le (c := c) hσ hσH hh_σ4 hb_meas
      have hstepA := lintegral_Ioo_measureH_exp_age_sub_sq_le hε hc hP U hU W hw
      have hchain : ∫⁻ s in Icc (σ / 2) (H1 + 1),
          sliceDiffSq c (periodize c (W : Profile → MeridC)) s h ≤
          4 * ENNReal.ofReal |h| *
            (ENNReal.ofReal (Real.exp 1 * (2 + H1)) *
              ENNReal.ofReal (10 * Real.exp 2 * ‖w_hd‖ ^ 2 + 2 * Real.exp 2 * ‖W‖ ^ 2)) :=
        hI₁_b.trans
          (hstepC.trans
            (mul_le_mul_of_nonneg_left
              (hstepB.trans (mul_le_mul_of_nonneg_left hstepA zero_le))
              zero_le))
      have hI₁ := hI₁_a.trans (mul_le_mul_of_nonneg_left hchain zero_le)
      refine (hsplit.trans
        (add_le_add
          (mul_le_mul_of_nonneg_left hI₁ zero_le)
          (mul_le_mul_of_nonneg_left hI₂ zero_le))).trans ?_
      exact shiftS_small_scalar_consolidation
        hG1 hH1_pos
        (two_add_H1_le_gamma (H1 := H1) χ χ1 hν hc hσ hL1 hγ hM)
        (cNorm8_nonneg χ)
        (cNorm8_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM)
        (norm_nonneg W) hW_le_NW
        (norm_nonneg w_hd) hwhd_le_NW
        hNW0 hh1

end UnforcedLeray.Short.PartIIa.N05FlowAux
