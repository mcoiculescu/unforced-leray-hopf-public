import UnforcedLeray.Lib.FreeStressCouplings.PhaseDrift
import UnforcedLeray.Lib.FreeStressCouplings.Shift
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Half-drift (`C_0^{1/2}`) bounds on the commuting dilation-drift group `phaseDilation P t`

For `v, w_hd : Yq P 2` satisfying `(FreeStress.phaseC0 P).HasPow (1 / 2) v w_hd`:
1. Pointwise `1/2`-Hölder group bound (for `PartII-a:N05/3/2`):
   `‖FreeStress.phaseDilation P t v - v‖ ≤ Real.sqrt (2 * |t|) * ‖w_hd‖`.
2. Integrated Slobodeckij bound over `t ∈ Ioi 0` (reused in `PartII-a:N05/3/1`):
   `∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-2 : ℝ)) * ‖FreeStress.phaseDilation P t v - v‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (5 * ‖w_hd‖ ^ 2)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa.N05FlowAux

open UnforcedLeray.PhaseSpace UnforcedLeray.FreeStress

/-- Standard `L²` norm-squared identity as a Lebesgue integral of `‖·‖ₑ ^ (2 : ℝ)`. -/
theorem lintegral_enorm_sq_eq_ofReal_norm_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (f : Lp E 2 μ) :
    ∫⁻ a, ‖(f : α → E) a‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (‖f‖ ^ 2) := by
  have hLp : eLpNorm (f : α → E) 2 μ = ENNReal.ofReal ‖f‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ)
    (f := (f : α → E)) two_ne_zero ENNReal.ofNat_ne_top
  rw [hLp, ENNReal.toReal_ofNat] at heq
  have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq.symm
  rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg f) (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_two] at hpow
  exact hpow

/-- Pointwise chord bounds on `phaseMul t σ - 1 = e^{2πiσt} - 1`. -/
theorem norm_phaseMul_sub_one_le_two (t σ : ℝ) :
    ‖phaseMul t σ - 1‖ ≤ 2 := by
  calc ‖phaseMul t σ - 1‖
      ≤ ‖phaseMul t σ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + 1 := by rw [norm_phaseMul, norm_one]
    _ = 2 := by norm_num

theorem norm_phaseMul_sub_one_le_mul (t σ : ℝ) :
    ‖phaseMul t σ - 1‖ ≤ |2 * π * σ| * |t| := by
  unfold phaseMul
  rw [mul_comm ((2 * π * σ * t : ℝ) : ℂ) Complex.I]
  calc ‖Complex.exp (Complex.I * ((2 * π * σ * t : ℝ) : ℂ)) - 1‖
      ≤ ‖(2 * π * σ * t : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |2 * π * σ| * |t| := by rw [Real.norm_eq_abs, abs_mul]

theorem norm_phaseMul_sub_one_sq_le (t σ : ℝ) :
    ‖phaseMul t σ - 1‖ ^ 2 ≤ 2 * |t| * (1 + |2 * π * σ|) := by
  have h1 := norm_phaseMul_sub_one_le_two t σ
  have h2 := norm_phaseMul_sub_one_le_mul t σ
  have h0 : 0 ≤ ‖phaseMul t σ - 1‖ := norm_nonneg _
  calc ‖phaseMul t σ - 1‖ ^ 2
      = ‖phaseMul t σ - 1‖ * ‖phaseMul t σ - 1‖ := sq _
    _ ≤ 2 * (|2 * π * σ| * |t|) := mul_le_mul h1 h2 h0 (by norm_num)
    _ ≤ 2 * ((1 + |2 * π * σ|) * |t|) := by gcongr; linarith [abs_nonneg (2 * π * σ)]
    _ = 2 * |t| * (1 + |2 * π * σ|) := by ring

theorem norm_phaseMul_sub_one_le_sqrt (t σ : ℝ) :
    ‖phaseMul t σ - 1‖ ≤ Real.sqrt (2 * |t|) * (1 + |2 * π * σ|) ^ (1 / 2 : ℝ) := by
  have hsym : 0 ≤ 1 + |2 * π * σ| := by positivity
  have hrhs0 : 0 ≤ Real.sqrt (2 * |t|) * (1 + |2 * π * σ|) ^ (1 / 2 : ℝ) := by positivity
  have hsq : ‖phaseMul t σ - 1‖ ^ 2 ≤
      (Real.sqrt (2 * |t|) * (1 + |2 * π * σ|) ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity),
      ← Real.rpow_natCast ((1 + |2 * π * σ|) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hsym,
      show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, Real.rpow_one]
    exact norm_phaseMul_sub_one_sq_le t σ
  exact (abs_le_of_sq_le_sq' hsq hrhs0).2

/-- Almost-everywhere Fourier representation of `phaseDilation P t v - v`. -/
theorem dilFourier_phaseDilation_sub_ae {P : ℝ} [Fact (0 < P)] (t : ℝ) (v : Yq P 2) :
    (dilFourier P (phaseDilation P t v - v) : ℝ → ShellL2 P) =ᵐ[volume]
      fun σ => (phaseMul t σ - 1) • (dilFourier P v : ℝ → ShellL2 P) σ := by
  have hmap : dilFourier P (phaseDilation P t v - v) =
      phaseMulOp t (dilFourier P v) - dilFourier P v := by
    rw [map_sub, dilFourier_phaseDilation]
  rw [hmap]
  filter_upwards [Lp.coeFn_sub (phaseMulOp t (dilFourier P v)) (dilFourier P v),
    phaseMulOp_ae t (dilFourier P v)] with σ hsub hmul
  rw [hsub, Pi.sub_apply, hmul, sub_smul, one_smul]

/-- **Pointwise `1/2`-Hölder group bound** on `phaseDilation P t` from `C_0^{1/2}`. -/
theorem norm_phaseDilation_sub_le {P : ℝ} [Fact (0 < P)] {v w_hd : Yq P 2}
    (hw : (phaseC0 P).HasPow (1 / 2) v w_hd) (t : ℝ) :
    ‖phaseDilation P t v - v‖ ≤ Real.sqrt (2 * |t|) * ‖w_hd‖ := by
  rw [← (dilFourier P).norm_map (phaseDilation P t v - v), ← (dilFourier P).norm_map w_hd]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [dilFourier_phaseDilation_sub_ae t v, hw] with σ hsub hpow
  change ‖(dilFourier P (phaseDilation P t v - v) : ℝ → ShellL2 P) σ‖ ≤
    Real.sqrt (2 * |t|) * ‖(dilFourier P w_hd : ℝ → ShellL2 P) σ‖
  have hpow' : (dilFourier P w_hd : ℝ → ShellL2 P) σ =
      (((1 + |2 * π * σ|) ^ (1 / 2 : ℝ) : ℝ) : ℂ) • (dilFourier P v : ℝ → ShellL2 P) σ := hpow
  rw [hsub, hpow', norm_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_phaseMul_sub_one_le_sqrt t σ) (norm_nonneg _)

/-- Corollary at `t = 2 * ε * h`: `‖phaseDilation P (2 * ε * h) v - v‖ ≤ 2 * √|ε * h| * ‖w_hd‖`. -/
theorem norm_phaseDilation_two_eps_mul_sub_le {P : ℝ} [Fact (0 < P)] {v w_hd : Yq P 2}
    (hw : (phaseC0 P).HasPow (1 / 2) v w_hd) (ε h : ℝ) :
    ‖phaseDilation P (2 * ε * h) v - v‖ ≤ 2 * Real.sqrt |ε * h| * ‖w_hd‖ := by
  have h1 := norm_phaseDilation_sub_le hw (2 * ε * h)
  have h2 : Real.sqrt (2 * |2 * ε * h|) = 2 * Real.sqrt |ε * h| := by
    rw [show 2 * ε * h = 2 * (ε * h) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      ← mul_assoc, show (2 : ℝ) * 2 = 2 ^ 2 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rwa [h2] at h1

/-- One-dimensional Slobodeckij symbol integral over `t ∈ Ioi 0`:
`∫⁻ t in Ioi 0, t^{-2} ‖phaseMul t σ - 1‖^2 ≤ 5 * (1 + |2πσ|)`. -/
theorem lintegral_Ioi_rpow_neg_two_phaseMul_sq_le (σ : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2) ≤
      ENNReal.ofReal (5 * (1 + |2 * π * σ|)) := by
  set A : ℝ := 1 + |2 * π * σ|
  have hA1 : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg (2 * π * σ)]
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  set c : ℝ := A⁻¹
  have hc0 : 0 < c := inv_pos.2 hA0
  have hunion : Ioi (0 : ℝ) = Ioc 0 c ∪ Ioi c := (Ioc_union_Ioi_eq_Ioi hc0.le).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) c) (Ioi c) :=
     Set.disjoint_left.2 fun t ht1 ht2 => not_lt_of_ge ht1.2 ht2
  rw [hunion, lintegral_union measurableSet_Ioi hdisj]
  have hleft : ∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2) ≤
      ENNReal.ofReal A := by
    have hpt : ∀ t ∈ Ioc (0 : ℝ) c,
        ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2) ≤ ENNReal.ofReal (A ^ 2) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      refine ENNReal.ofReal_le_ofReal ?_
      have hch : ‖phaseMul t σ - 1‖ ≤ A * t := by
        calc ‖phaseMul t σ - 1‖
            ≤ |2 * π * σ| * |t| := norm_phaseMul_sub_one_le_mul t σ
          _ = |2 * π * σ| * t := by rw [abs_of_pos ht0]
          _ ≤ A * t := by dsimp [A]; gcongr; linarith
      have hsq : ‖phaseMul t σ - 1‖ ^ 2 ≤ A ^ 2 * t ^ 2 := by
        calc ‖phaseMul t σ - 1‖ ^ 2
            ≤ (A * t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hch 2
          _ = A ^ 2 * t ^ 2 := by ring
      calc t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2
          ≤ t ^ (-2 : ℝ) * (A ^ 2 * t ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg ht0.le _)
        _ = A ^ 2 * (t ^ (-2 : ℝ) * t ^ (2 : ℝ)) := by rw [Real.rpow_two]; ring
        _ = A ^ 2 := by rw [← Real.rpow_add ht0]; norm_num
    calc ∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2)
        ≤ ∫⁻ _t in Ioc (0 : ℝ) c, ENNReal.ofReal (A ^ 2) :=
          setLIntegral_mono' measurableSet_Ioc hpt
      _ = ENNReal.ofReal (A ^ 2) * volume (Ioc (0 : ℝ) c) := by simp
      _ = ENNReal.ofReal A := by
          rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          dsimp [c]
          field_simp
  have hright : ∫⁻ t in Ioi c, ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2) ≤
      ENNReal.ofReal (4 * A) := by
    have hpt : ∀ t ∈ Ioi c,
        ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2) ≤
          ENNReal.ofReal (4 * t ^ (-2 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := hc0.trans ht
      refine ENNReal.ofReal_le_ofReal ?_
      have h4 : ‖phaseMul t σ - 1‖ ^ 2 ≤ 4 := by
        calc ‖phaseMul t σ - 1‖ ^ 2
            ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_phaseMul_sub_one_le_two t σ) 2
          _ = 4 := by norm_num
      calc t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2
          ≤ t ^ (-2 : ℝ) * 4 := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg ht0.le _)
        _ = 4 * t ^ (-2 : ℝ) := by ring
    have hint : IntegrableOn (fun t : ℝ => 4 * t ^ (-2 : ℝ)) (Ioi c) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc0).const_mul 4
    have hval : ∫ t in Ioi c, 4 * t ^ (-2 : ℝ) = 4 * A := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc0]
      dsimp [c]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, inv_inv]
      ring
    calc ∫⁻ t in Ioi c, ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2)
        ≤ ∫⁻ t in Ioi c, ENNReal.ofReal (4 * t ^ (-2 : ℝ)) :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = ENNReal.ofReal (∫ t in Ioi c, 4 * t ^ (-2 : ℝ)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint]
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : 0 < t := hc0.trans ht
          positivity
      _ = ENNReal.ofReal (4 * A) := by rw [hval]
  calc (∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2)) +
        ∫⁻ t in Ioi c, ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2)
      ≤ ENNReal.ofReal A + ENNReal.ofReal (4 * A) := add_le_add hleft hright
    _ = ENNReal.ofReal (5 * A) := by
        rw [← ENNReal.ofReal_add hA0.le (by positivity)]
        congr 1
        ring

/-- **Integrated Slobodeckij bound** on `phaseDilation P t v - v` over `t ∈ Ioi 0` from `C_0^{1/2}`. -/
theorem lintegral_Ioi_phaseDilation_sub_sq_le {P : ℝ} [Fact (0 < P)] {v w_hd : Yq P 2}
    (hw : (phaseC0 P).HasPow (1 / 2) v w_hd) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-2 : ℝ)) * ‖phaseDilation P t v - v‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (5 * ‖w_hd‖ ^ 2) := by
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (-2 : ℝ)) * ‖phaseDilation P t v - v‖ₑ ^ (2 : ℝ) =
        ∫⁻ σ : ℝ, ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2) *
          ‖(dilFourier P v : ℝ → ShellL2 P) σ‖ₑ ^ (2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hnorm : ‖phaseDilation P t v - v‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (‖dilFourier P (phaseDilation P t v - v)‖ ^ 2) := by
      rw [← ofReal_norm, ← (dilFourier P).norm_map (phaseDilation P t v - v),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    rw [hnorm, ← lintegral_enorm_sq_eq_ofReal_norm_sq (dilFourier P (phaseDilation P t v - v)),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [dilFourier_phaseDilation_sub_ae t v] with σ hsub
    rw [hsub, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← mul_assoc]
    congr 1
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpoint]
  have hm_phase : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 ^ (-2 : ℝ) * ‖phaseMul p.1 p.2 - 1‖ ^ 2) := by
    unfold phaseMul
    fun_prop
  have hm_v : AEMeasurable (fun σ : ℝ => ‖(dilFourier P v : ℝ → ShellL2 P) σ‖ₑ ^ (2 : ℝ)) volume :=
    (Lp.aestronglyMeasurable (dilFourier P v)).enorm.pow_const (2 : ℝ)
  have hm_prod : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-2 : ℝ) * ‖phaseMul p.1 p.2 - 1‖ ^ 2) *
        ‖(dilFourier P v : ℝ → ShellL2 P) p.2‖ₑ ^ (2 : ℝ))
      (((volume : Measure ℝ).restrict (Ioi 0)).prod (volume : Measure ℝ)) :=
    hm_phase.aemeasurable.mul (hm_v.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  rw [lintegral_lintegral_swap hm_prod]
  have hw_ae : ∀ᵐ σ : ℝ ∂volume,
      ENNReal.ofReal (5 * (1 + |2 * π * σ|)) * ‖(dilFourier P v : ℝ → ShellL2 P) σ‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal 5 * ‖(dilFourier P w_hd : ℝ → ShellL2 P) σ‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hw] with σ hpow
    have hpow' : (dilFourier P w_hd : ℝ → ShellL2 P) σ =
        (((1 + |2 * π * σ|) ^ (1 / 2 : ℝ) : ℝ) : ℂ) • (dilFourier P v : ℝ → ShellL2 P) σ := hpow
    have hsym0 : 0 ≤ 1 + |2 * π * σ| := by positivity
    rw [hpow', enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← mul_assoc]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hsym0 _),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hsym0 _) (by norm_num),
      ← Real.rpow_mul hsym0, show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
  calc ∫⁻ σ : ℝ, ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2) *
            ‖(dilFourier P v : ℝ → ShellL2 P) σ‖ₑ ^ (2 : ℝ)
      = ∫⁻ σ : ℝ, (∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (-2 : ℝ) * ‖phaseMul t σ - 1‖ ^ 2)) *
            ‖(dilFourier P v : ℝ → ShellL2 P) σ‖ₑ ^ (2 : ℝ) := by
        refine lintegral_congr fun σ => ?_
        exact lintegral_mul_const _ (by unfold phaseMul; fun_prop)
    _ ≤ ∫⁻ σ : ℝ, ENNReal.ofReal (5 * (1 + |2 * π * σ|)) *
          ‖(dilFourier P v : ℝ → ShellL2 P) σ‖ₑ ^ (2 : ℝ) := by
        refine lintegral_mono fun σ => ?_
        gcongr
        exact lintegral_Ioi_rpow_neg_two_phaseMul_sq_le σ
    _ = ∫⁻ σ : ℝ, ENNReal.ofReal 5 * ‖(dilFourier P w_hd : ℝ → ShellL2 P) σ‖ₑ ^ (2 : ℝ) :=
        lintegral_congr_ae hw_ae
    _ = ENNReal.ofReal 5 * ∫⁻ σ : ℝ, ‖(dilFourier P w_hd : ℝ → ShellL2 P) σ‖ₑ ^ (2 : ℝ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (5 * ‖w_hd‖ ^ 2) := by
        rw [lintegral_enorm_sq_eq_ofReal_norm_sq (dilFourier P w_hd), (dilFourier P).norm_map,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]

end UnforcedLeray.Short.PartIIa.N05FlowAux
