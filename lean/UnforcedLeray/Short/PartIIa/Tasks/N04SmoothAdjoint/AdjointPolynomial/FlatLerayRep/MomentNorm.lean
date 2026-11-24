import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_1
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatLerayRep.IterDecay
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.ObsBoxS1
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!


Source of record: `the November 2 reference manuscript`,
lines 1723–1726 and 1800–1823 (Lemma `near:adjoint-polynomial`).

Proves `theorem flatLerayMomentNormBound : FlatLerayMomentNormBound` in namespace
`UnforcedLeray.Short.PartIIa`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
open UnforcedLeray.Short.PartIIIb.NearInst.Masked
open IterDecayAux ObsBoxS1Aux

namespace MomentNormAux

/-! ### 1. `L²` norm-squared identity and `PepsC 0 c` contraction -/

lemma toReal_eLpNorm_two_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} {f : α → E} (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hm2 : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) μ := hf.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ => by positivity) hm2,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.toReal_pow]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat]
  norm_num

lemma memLp_norm_toLp_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [Lp.norm_toLp, toReal_eLpNorm_two_sq hf.aestronglyMeasurable]

lemma norm_cvec_sq (w : Fin 2 → ℝ) : ‖cvec w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
  simp [cvec, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma integral_cvec_lerayField_sq_le {c : ℝ} (hc : 0 < c) {F : Chart → Fin 2 → ℝ}
    (hF : IsForceField c F) :
    Integrable (fun p => ‖cvec (lerayField c F p)‖ ^ 2) (measureH c) ∧
    Integrable (fun p => ‖cvec (F p)‖ ^ 2) (measureH c) ∧
    ∫ p, ‖cvec (lerayField c F p)‖ ^ 2 ∂(measureH c) ≤
      ∫ p, ‖cvec (F p)‖ ^ 2 ∂(measureH c) := by
  obtain ⟨hWs, hWp, hWb, -, hWe, hWdiv⟩ := lerayFieldProps c hc F hF
  obtain ⟨hus, hub, -⟩ := lerayPotSmooth c hc F hF
  obtain ⟨Cd, κd, hκd, hdec⟩ := lerayPotDecay c hc F hF
  rcases hF with ⟨_, hFp, s0, s1, _, hs0, hFb⟩
  have huband : ∀ p, lerayPot c F p ≠ 0 → p.1 ∈ Icc s0 s1 :=
    lerayPot_band (fun p hp => (hFb p hp).1)
  have hubdd : ∃ C : ℝ, ∀ p, |lerayPot c F p| ≤ C := by
    obtain ⟨C, hC⟩ := hub 0
    refine ⟨C, fun p => ?_⟩
    have := hC p
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hWm := memLpOfDecay c hc (lerayField c F) (fun i => (hWs i).continuous) hWb hWe
  have hVm := memLpOfDecay c hc (flatGrad (lerayPot c F)) (flatGrad_continuous hus)
    ⟨s0, s1, hs0, flatGrad_band huband⟩ ⟨Cd, κd, hκd, flatGrad_decay hdec⟩
  have ha := smoothSolenoidal c hc (lerayField c F) hWs hWp hWdiv hWm
  have hb := smoothGradPerp c hc (lerayPot c F) hus (lerayPot_periodic hFp)
    ⟨s0, s1, hs0, huband⟩ hubdd ⟨Cd, κd, hκd, hdec⟩ hVm
  have hF_eq : (fun p : Profile => cvec (F p)) =
      (fun p => cvec (lerayField c F p)) + (fun p => cvec (flatGrad (lerayPot c F) p)) := by
    funext p
    ext i
    simp only [Pi.add_apply, PiLp.add_apply, cvec, lerayField]
    push_cast
    ring
  have hF_lp : MemLp (fun p => cvec (F p)) 2 (measureH c) := by
    rw [hF_eq]
    exact hWm.add hVm
  have hsum : hF_lp.toLp _ = hWm.toLp _ + hVm.toLp _ := by
    apply Lp.ext
    filter_upwards [hF_lp.coeFn_toLp, Lp.coeFn_add (hWm.toLp _) (hVm.toLp _),
      hWm.coeFn_toLp, hVm.coeFn_toLp] with p h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4]
    exact congrFun hF_eq p
  have hP : PepsC 0 c (hF_lp.toLp _) = hWm.toLp _ := by
    rw [hsum, pepsC_eq_of_decomp ha hb]
  have hle_norm : ‖hWm.toLp _‖ ≤ ‖hF_lp.toLp _‖ := by
    rw [← hP]
    exact Submodule.norm_starProjection_apply_le _ _
  refine ⟨hWm.integrable_norm_pow (by norm_num), hF_lp.integrable_norm_pow (by norm_num), ?_⟩
  rw [← memLp_norm_toLp_sq hWm, ← memLp_norm_toLp_sq hF_lp]
  exact pow_le_pow_left₀ (norm_nonneg _) hle_norm 2

/-! ### 2. Explicit `c`-dependent constant for `cylKerAsym` -/

lemma cylKerAsym_explicit {c : ℝ} (hc : 0 < c) {y : ℝ × ℝ} (hy : 1 ≤ |y.2|) :
    |cylKer c 0 y| ≤ 2 * (1 + c + c⁻¹) * Real.exp (-(cylFreq c * |y.2|)) ∧
    |cylKer c 1 y - cylFreq c / (4 * Real.pi) * Real.sign y.2| ≤
      2 * (1 + c + c⁻¹) * Real.exp (-(cylFreq c * |y.2|)) := by
  have ha : 0 < cylFreq c := dd_freq_pos c hc
  have hκ := cylKA_kappa_pos ha
  have hpos4 : 0 < cylFreq c / (4 * Real.pi) := div_pos ha (by positivity)
  set K : ℝ := cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2))
  have hK_le : K ≤ 2 * (1 + c + c⁻¹) := by
    have hcosh := cosh_lower_bd (cylFreq c)
    have ha2 : 0 < cylFreq c ^ 2 / 2 := by positivity
    have hcosh1 : 0 < Real.cosh (cylFreq c) - 1 := by linarith
    have hcosh_pos : 0 < Real.cosh (cylFreq c) := by linarith
    have h1 : 1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) =
        2 + 2 / (Real.cosh (cylFreq c) - 1) := by
      have hne1 : Real.cosh (cylFreq c) ≠ 0 := hcosh_pos.ne'
      have hne2 : Real.cosh (cylFreq c) - 1 ≠ 0 := hcosh1.ne'
      field_simp
      ring
    have h2 : 2 / (Real.cosh (cylFreq c) - 1) ≤ 2 / (cylFreq c ^ 2 / 2) :=
      div_le_div_of_nonneg_left (by norm_num) ha2 (by linarith)
    have hfreq : cylFreq c / (4 * Real.pi) * 2 = c⁻¹ := by
      unfold cylFreq
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp
      ring
    have hfreq2 : c⁻¹ * (2 / (cylFreq c ^ 2 / 2)) = c / Real.pi ^ 2 := by
      unfold cylFreq
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      have hc' : c ≠ 0 := hc.ne'
      field_simp
    have hpi_sq : 1 ≤ Real.pi ^ 2 := by
      have := Real.pi_gt_three
      nlinarith
    have hc_pi : c / Real.pi ^ 2 ≤ c := div_le_self hc.le hpi_sq
    calc K = c⁻¹ * (2 + 2 / (Real.cosh (cylFreq c) - 1)) := by
          change cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2)) = _
          rw [hfreq, h1]
      _ ≤ c⁻¹ * (2 + 2 / (cylFreq c ^ 2 / 2)) := by gcongr
      _ = 2 * c⁻¹ + c⁻¹ * (2 / (cylFreq c ^ 2 / 2)) := by ring
      _ = 2 * c⁻¹ + c / Real.pi ^ 2 := by rw [hfreq2]
      _ ≤ 2 * c⁻¹ + c := by linarith
      _ ≤ 2 * (1 + c + c⁻¹) := by linarith
  have hK0 : cylKer c 0 y = cylFreq c / (4 * Real.pi) * Real.sin (cylFreq c * y.1) / cylDen c y := by
    simp [cylKer, cylNum]
  have hK1 : cylKer c 1 y = cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * y.2) / cylDen c y := by
    simp [cylKer, cylNum]
  have hgap : (1 - (Real.cosh (cylFreq c))⁻¹) / 2 * Real.exp (cylFreq c * |y.2|) ≤ cylDen c y :=
    cylKA_cosh_gap ha y.1 y.2 hy
  have hDpos : 0 < cylDen c y := lt_of_lt_of_le (mul_pos hκ (Real.exp_pos _)) hgap
  have hinv : 1 / cylDen c y ≤
      1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) * Real.exp (-(cylFreq c * |y.2|)) :=
    cylKA_inv_den ha y.1 y.2 hy
  have hy0 : y.2 ≠ 0 := by
    rintro h
    rw [h, abs_zero] at hy
    norm_num at hy
  have hE : 0 ≤ Real.exp (-(cylFreq c * |y.2|)) := (Real.exp_pos _).le
  constructor
  · rw [hK0, abs_div, abs_mul, abs_of_pos hpos4, abs_of_pos hDpos]
    have hsin : |Real.sin (cylFreq c * y.1)| ≤ 1 := Real.abs_sin_le_one _
    have h1 : cylFreq c / (4 * Real.pi) * |Real.sin (cylFreq c * y.1)| ≤ cylFreq c / (4 * Real.pi) := by
      calc cylFreq c / (4 * Real.pi) * |Real.sin (cylFreq c * y.1)|
          ≤ cylFreq c / (4 * Real.pi) * 1 := mul_le_mul_of_nonneg_left hsin hpos4.le
        _ = cylFreq c / (4 * Real.pi) := mul_one _
    have h2 := div_le_div_of_nonneg_right h1 hDpos.le
    have hXY : 0 ≤ cylFreq c / (4 * Real.pi) * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
        Real.exp (-(cylFreq c * |y.2|))) :=
      mul_nonneg hpos4.le (mul_nonneg (div_nonneg zero_le_one hκ.le) hE)
    calc cylFreq c / (4 * Real.pi) * |Real.sin (cylFreq c * y.1)| / cylDen c y
        ≤ cylFreq c / (4 * Real.pi) / cylDen c y := h2
      _ = cylFreq c / (4 * Real.pi) * (1 / cylDen c y) := by ring
      _ ≤ cylFreq c / (4 * Real.pi) * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
            Real.exp (-(cylFreq c * |y.2|))) := mul_le_mul_of_nonneg_left hinv hpos4.le
      _ ≤ 2 * (cylFreq c / (4 * Real.pi) * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
            Real.exp (-(cylFreq c * |y.2|)))) := by linarith
      _ = K * Real.exp (-(cylFreq c * |y.2|)) := by ring
      _ ≤ 2 * (1 + c + c⁻¹) * Real.exp (-(cylFreq c * |y.2|)) :=
          mul_le_mul_of_nonneg_right hK_le hE
  · rcases lt_or_gt_of_ne hy0 with hneg | hposy
    · have hx : cylFreq c * y.2 < 0 := mul_neg_of_pos_of_neg ha hneg
      have hs2 : Real.sinh (cylFreq c * y.2) =
          Real.exp (cylFreq c * y.2) - Real.cosh (cylFreq c * y.2) := by
        linarith [Real.cosh_add_sinh (cylFreq c * y.2)]
      have hDne : Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) ≠ 0 := hDpos.ne'
      have hkey : cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * y.2) / cylDen c y -
          cylFreq c / (4 * Real.pi) * -1 =
          cylFreq c / (4 * Real.pi) * (Real.exp (cylFreq c * y.2) - Real.cos (cylFreq c * y.1)) /
            cylDen c y := by
        unfold cylDen
        rw [hs2]
        field_simp
        ring
      have hexp1 : Real.exp (cylFreq c * y.2) ≤ 1 := Real.exp_le_one_iff.mpr hx.le
      have hb : |Real.exp (cylFreq c * y.2) - Real.cos (cylFreq c * y.1)| ≤ 2 := by
        rw [abs_le]
        constructor
        · linarith [Real.cos_le_one (cylFreq c * y.1), Real.exp_pos (cylFreq c * y.2)]
        · linarith [Real.neg_one_le_cos (cylFreq c * y.1), hexp1]
      rw [hK1, Real.sign_of_neg hneg, hkey, abs_div, abs_mul, abs_of_pos hpos4, abs_of_pos hDpos]
      calc cylFreq c / (4 * Real.pi) * |Real.exp (cylFreq c * y.2) - Real.cos (cylFreq c * y.1)| /
            cylDen c y
          ≤ cylFreq c / (4 * Real.pi) * 2 / cylDen c y :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hpos4.le) hDpos.le
        _ = cylFreq c / (4 * Real.pi) * 2 * (1 / cylDen c y) := by ring
        _ ≤ cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
              Real.exp (-(cylFreq c * |y.2|))) :=
            mul_le_mul_of_nonneg_left hinv (mul_nonneg hpos4.le zero_le_two)
        _ = K * Real.exp (-(cylFreq c * |y.2|)) := by ring
        _ ≤ 2 * (1 + c + c⁻¹) * Real.exp (-(cylFreq c * |y.2|)) :=
            mul_le_mul_of_nonneg_right hK_le hE
    · have hx : 0 < cylFreq c * y.2 := mul_pos ha hposy
      have hs1 : Real.sinh (cylFreq c * y.2) =
          Real.cosh (cylFreq c * y.2) - Real.exp (-(cylFreq c * y.2)) := by
        linarith [Real.cosh_sub_sinh (cylFreq c * y.2)]
      have hDne : Real.cosh (cylFreq c * y.2) - Real.cos (cylFreq c * y.1) ≠ 0 := hDpos.ne'
      have hkey : cylFreq c / (4 * Real.pi) * Real.sinh (cylFreq c * y.2) / cylDen c y -
          cylFreq c / (4 * Real.pi) * 1 =
          cylFreq c / (4 * Real.pi) * (Real.cos (cylFreq c * y.1) - Real.exp (-(cylFreq c * y.2))) /
            cylDen c y := by
        unfold cylDen
        rw [hs1]
        field_simp
        ring
      have hexp1 : Real.exp (-(cylFreq c * y.2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hb : |Real.cos (cylFreq c * y.1) - Real.exp (-(cylFreq c * y.2))| ≤ 2 := by
        rw [abs_le]
        constructor
        · linarith [Real.neg_one_le_cos (cylFreq c * y.1), hexp1]
        · linarith [Real.cos_le_one (cylFreq c * y.1), Real.exp_pos (-(cylFreq c * y.2))]
      rw [hK1, Real.sign_of_pos hposy, hkey, abs_div, abs_mul, abs_of_pos hpos4, abs_of_pos hDpos]
      calc cylFreq c / (4 * Real.pi) * |Real.cos (cylFreq c * y.1) - Real.exp (-(cylFreq c * y.2))| /
            cylDen c y
          ≤ cylFreq c / (4 * Real.pi) * 2 / cylDen c y :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hpos4.le) hDpos.le
        _ = cylFreq c / (4 * Real.pi) * 2 * (1 / cylDen c y) := by ring
        _ ≤ cylFreq c / (4 * Real.pi) * 2 * (1 / ((1 - (Real.cosh (cylFreq c))⁻¹) / 2) *
              Real.exp (-(cylFreq c * |y.2|))) :=
            mul_le_mul_of_nonneg_left hinv (mul_nonneg hpos4.le zero_le_two)
        _ = K * Real.exp (-(cylFreq c * |y.2|)) := by ring
        _ ≤ 2 * (1 + c + c⁻¹) * Real.exp (-(cylFreq c * |y.2|)) :=
            mul_le_mul_of_nonneg_right hK_le hE

/-! ### 3. 1D `intervalIntegral` Cauchy-Schwarz and Window Shift -/

lemma intervalIntegral_sq_le {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, (f x) ^ 2 := by
  set L : ℝ := b - a
  set I : ℝ := ∫ x in a..b, f x
  have hL : 0 ≤ L := sub_nonneg.mpr hab
  rcases hL.eq_or_lt with hL0 | hLpos
  · have hab_eq : a = b := by linarith
    subst hab_eq
    simp [I]
  · have hpt : ∀ x ∈ Icc a b, 2 * L * I * f x - I ^ 2 ≤ L ^ 2 * (f x) ^ 2 := by
      intro x _
      nlinarith [sq_nonneg (L * f x - I)]
    have hi1 : IntervalIntegrable (fun x => 2 * L * I * f x - I ^ 2) volume a b :=
      ((hf.const_mul (2 * L * I)).sub continuous_const).intervalIntegrable a b
    have hi2 : IntervalIntegrable (fun x => L ^ 2 * (f x) ^ 2) volume a b :=
      ((hf.pow 2).const_mul (L ^ 2)).intervalIntegrable a b
    have hmono := intervalIntegral.integral_mono_on hab hi1 hi2 hpt
    have hlhs : ∫ x in a..b, (2 * L * I * f x - I ^ 2) = L * I ^ 2 := by
      rw [intervalIntegral.integral_sub ((hf.const_mul _).intervalIntegrable a b)
        (intervalIntegrable_const),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
      change 2 * L * I * I - L * I ^ 2 = L * I ^ 2
      ring
    have hrhs : ∫ x in a..b, L ^ 2 * (f x) ^ 2 = L ^ 2 * ∫ x in a..b, (f x) ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    rw [hlhs, hrhs] at hmono
    nlinarith

lemma window_shift_eq {c L1 : ℝ} (hc : 0 < c) (hL1 : 0 ≤ L1) {h : ℝ × ℝ → ℝ}
    (hh : Continuous h) (hper : ∀ q η : ℝ, h (q + c, η) = h (q, η)) (x : ℝ × ℝ) :
    ∫ y in Ioc (-(c / 2)) (c / 2) ×ˢ Icc (x.2 - L1) (x.2 + L1), h (x - y) =
      ∫ q in (0 : ℝ)..c, ∫ η in (-L1)..L1, h (q, η) := by
  have hcomp : Continuous (fun y : ℝ × ℝ => h (x - y)) :=
    hh.comp (continuous_const.sub continuous_id)
  have hint : IntegrableOn (fun y : ℝ × ℝ => h (x - y))
      (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (x.2 - L1) (x.2 + L1)) := by
    have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (x.2 - L1) (x.2 + L1)) :=
      isCompact_Icc.prod isCompact_Icc
    exact (hcomp.continuousOn.integrableOn_compact hK).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint]
  have hinner : ∀ y1 : ℝ, ∫ y2 in Icc (x.2 - L1) (x.2 + L1), h (x - (y1, y2)) =
      ∫ η in (-L1)..L1, h (x.1 - y1, η) := by
    intro y1
    change ∫ y2 in Icc (x.2 - L1) (x.2 + L1), h (x.1 - y1, x.2 - y2) = _
    rw [← setIntegral_congr_set Ioc_ae_eq_Icc, ← intervalIntegral.integral_of_le (by linarith)]
    have hsub := intervalIntegral.integral_comp_sub_left (fun η => h (x.1 - y1, η)) x.2
      (a := x.2 - L1) (b := x.2 + L1)
    have ha : x.2 - (x.2 + L1) = -L1 := by ring
    have hb : x.2 - (x.2 - L1) = L1 := by ring
    rw [ha, hb] at hsub
    exact hsub
  simp_rw [hinner]
  set g : ℝ → ℝ := fun q => ∫ η in (-L1)..L1, h (q, η)
  have hg_per : Function.Periodic g c := by
    intro q
    change ∫ η in (-L1)..L1, h (q + c, η) = ∫ η in (-L1)..L1, h (q, η)
    congr 1
    ext η
    exact hper q η
  rw [← intervalIntegral.integral_of_le (by linarith)]
  have hsub1 := intervalIntegral.integral_comp_sub_left g x.1 (a := -(c / 2)) (b := c / 2)
  have heq : x.1 - -(c / 2) = (x.1 - c / 2) + c := by ring
  rw [hsub1, heq, hg_per.intervalIntegral_add_eq (x.1 - c / 2) 0, zero_add]

/-- Slice `L²` integral of a real chart field `G` over `(0, c] × [-L1, L1]`. -/
def sliceSq (c L1 : ℝ) (G : Chart → Fin 2 → ℝ) (s : ℝ) : ℝ :=
  ∫ q in (0 : ℝ)..c, ∫ η in (-L1)..L1, (G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2)

lemma continuous_sliceSq (c L1 : ℝ) {G : Chart → Fin 2 → ℝ}
    (hGs : ∀ l, ContDiff ℝ ∞ (fun p => G p l)) :
    Continuous (sliceSq c L1 G) := by
  have hcont3 : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      G (p.1.1, p.1.2, p.2) 0 ^ 2 + G (p.1.1, p.1.2, p.2) 1 ^ 2) := by
    have h0 : Continuous (fun p : (ℝ × ℝ) × ℝ => G (p.1.1, p.1.2, p.2) 0) :=
      (hGs 0).continuous.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
    have h1 : Continuous (fun p : (ℝ × ℝ) × ℝ => G (p.1.1, p.1.2, p.2) 1) :=
      (hGs 1).continuous.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
    exact (h0.pow 2).add (h1.pow 2)
  have hcont2 : Continuous (fun sq : ℝ × ℝ =>
      ∫ η in (-L1)..L1, (G (sq.1, sq.2, η) 0 ^ 2 + G (sq.1, sq.2, η) 1 ^ 2)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (sq : ℝ × ℝ) (η : ℝ) =>
        G (sq.1, sq.2, η) 0 ^ 2 + G (sq.1, sq.2, η) 1 ^ 2)
      hcont3 (-L1) L1
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume)
    (f := fun (s : ℝ) (q : ℝ) => ∫ η in (-L1)..L1, (G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2))
    hcont2 0 c

lemma sliceSq_nonneg {c L1 : ℝ} (hc : 0 < c) (hL1 : 0 ≤ L1) (G : Chart → Fin 2 → ℝ) (s : ℝ) :
    0 ≤ sliceSq c L1 G s := by
  unfold sliceSq
  refine intervalIntegral.integral_nonneg (by linarith) fun q _ => ?_
  exact intervalIntegral.integral_nonneg (by linarith) fun η _ => by positivity

lemma sliceSq_eq_zero_of_not_mem_Icc {c σ H1 L1 : ℝ} {G : Chart → Fin 2 → ℝ}
    (hG_supp : ∀ p : Chart, G p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    {s : ℝ} (hs : s ∉ Icc σ H1) :
    sliceSq c L1 G s = 0 := by
  have h0 : ∀ q η : ℝ, G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2 = 0 := by
    intro q η
    have hG0 : G (s, q, η) = 0 := by
      by_contra hne
      exact hs ⟨(hG_supp (s, q, η) hne).1, (hG_supp (s, q, η) hne).2.1⟩
    simp [hG0]
  unfold sliceSq
  simp [h0]

lemma gSlice_sq_le_sliceSq {c L1 : ℝ} (hc : 0 < c) (hL1 : 0 ≤ L1) {G : Chart → Fin 2 → ℝ}
    (hGs : ∀ l, ContDiff ℝ ∞ (fun p => G p l)) (s : ℝ) :
    (∫ q in (0 : ℝ)..c, ∫ η in (-L1)..L1, (|G (s, q, η) 0| + |G (s, q, η) 1|)) ^ 2 ≤
      4 * c * L1 * sliceSq c L1 G s := by
  have hcont_h : Continuous (fun x : ℝ × ℝ => |G (s, x.1, x.2) 0| + |G (s, x.1, x.2) 1|) := by
    have h0 : Continuous (fun x : ℝ × ℝ => G (s, x) 0) :=
      (hGs 0).continuous.comp (continuous_const.prodMk continuous_id)
    have h1 : Continuous (fun x : ℝ × ℝ => G (s, x) 1) :=
      (hGs 1).continuous.comp (continuous_const.prodMk continuous_id)
    exact h0.abs.add h1.abs
  set f1 : ℝ → ℝ := fun q => ∫ η in (-L1)..L1, (|G (s, q, η) 0| + |G (s, q, η) 1|)
  have hf1_cont : Continuous f1 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (q : ℝ) (η : ℝ) => |G (s, q, η) 0| + |G (s, q, η) 1|)
      hcont_h (-L1) L1
  have hcs1 := intervalIntegral_sq_le hc.le hf1_cont
  rw [sub_zero] at hcs1
  have hf1_sq : ∀ q : ℝ, (f1 q) ^ 2 ≤
      4 * L1 * ∫ η in (-L1)..L1, (G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2) := by
    intro q
    have hη_cont : Continuous (fun η : ℝ => |G (s, q, η) 0| + |G (s, q, η) 1|) :=
      hcont_h.comp (continuous_const.prodMk continuous_id)
    have hcs2 := intervalIntegral_sq_le (by linarith : -L1 ≤ L1) hη_cont
    have hlen : L1 - -L1 = 2 * L1 := by ring
    rw [hlen] at hcs2
    have hpt : ∀ η ∈ Icc (-L1) L1,
        (|G (s, q, η) 0| + |G (s, q, η) 1|) ^ 2 ≤
          2 * (G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2) := by
      intro η _
      nlinarith [sq_nonneg (|G (s, q, η) 0| - |G (s, q, η) 1|),
        sq_abs (G (s, q, η) 0), sq_abs (G (s, q, η) 1)]
    have hnorm_cont : Continuous (fun η : ℝ => G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2) := by
      have h0 : Continuous (fun η : ℝ => G (s, q, η) 0) :=
        (hGs 0).continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      have h1 : Continuous (fun η : ℝ => G (s, q, η) 1) :=
        (hGs 1).continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      exact (h0.pow 2).add (h1.pow 2)
    have hi_lhs : IntervalIntegrable (fun η => (|G (s, q, η) 0| + |G (s, q, η) 1|) ^ 2)
        volume (-L1) L1 := (hη_cont.pow 2).intervalIntegrable _ _
    have hi_rhs : IntervalIntegrable (fun η => 2 * (G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2))
        volume (-L1) L1 := (hnorm_cont.const_mul 2).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (by linarith : -L1 ≤ L1) hi_lhs hi_rhs hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    calc (f1 q) ^ 2
        ≤ 2 * L1 * ∫ η in (-L1)..L1, (|G (s, q, η) 0| + |G (s, q, η) 1|) ^ 2 := hcs2
      _ ≤ 2 * L1 * (2 * ∫ η in (-L1)..L1, (G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = 4 * L1 * ∫ η in (-L1)..L1, (G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2) := by ring
  have hinner_cont : Continuous (fun q : ℝ =>
      ∫ η in (-L1)..L1, (G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2)) := by
    have hcont3 : Continuous (fun qη : ℝ × ℝ =>
        G (s, qη.1, qη.2) 0 ^ 2 + G (s, qη.1, qη.2) 1 ^ 2) := by
      have h0 : Continuous (fun qη : ℝ × ℝ => G (s, qη) 0) :=
        (hGs 0).continuous.comp (continuous_const.prodMk continuous_id)
      have h1 : Continuous (fun qη : ℝ × ℝ => G (s, qη) 1) :=
        (hGs 1).continuous.comp (continuous_const.prodMk continuous_id)
      exact (h0.pow 2).add (h1.pow 2)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (q : ℝ) (η : ℝ) => G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2)
      hcont3 (-L1) L1
  have hiq_lhs : IntervalIntegrable (fun q => (f1 q) ^ 2) volume 0 c :=
    (hf1_cont.pow 2).intervalIntegrable _ _
  have hiq_rhs : IntervalIntegrable
      (fun q => 4 * L1 * ∫ η in (-L1)..L1, (G (s, q, η) 0 ^ 2 + G (s, q, η) 1 ^ 2))
      volume 0 c :=
    (hinner_cont.const_mul (4 * L1)).intervalIntegrable _ _
  have hmono_q := intervalIntegral.integral_mono_on hc.le hiq_lhs hiq_rhs (fun q _ => hf1_sq q)
  rw [intervalIntegral.integral_const_mul] at hmono_q
  calc (∫ q in (0 : ℝ)..c, f1 q) ^ 2
      ≤ c * ∫ q in (0 : ℝ)..c, (f1 q) ^ 2 := hcs1
    _ ≤ c * (4 * L1 * sliceSq c L1 G s) :=
        mul_le_mul_of_nonneg_left hmono_q hc.le
    _ = 4 * c * L1 * sliceSq c L1 G s := by ring

lemma integrableOn_cvec_sq_cell {c σ H1 L1 : ℝ} {G : Chart → Fin 2 → ℝ}
    (hGs : ∀ l, ContDiff ℝ ∞ (fun p => G p l))
    (hG_supp : ∀ p : Chart, G p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    IntegrableOn (fun p : Chart => ‖cvec (G p)‖ ^ 2) (cell c) := by
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := dtdBox σ H1 c L1) ?_
    (measurableSet_cell c) fun p hp => ?_
  · refine ContinuousOn.integrableOn_compact (dtdBox_compact σ H1 c L1) ?_
    refine Continuous.continuousOn ?_
    simp_rw [norm_cvec_sq]
    exact (((hGs 0).continuous).pow 2).add (((hGs 1).continuous).pow 2)
  · obtain ⟨hpcell, hpnot⟩ := hp
    have hG0 : G p = 0 := by
      by_contra hne
      obtain ⟨h1, h2, h3⟩ := hG_supp p hne
      exact hpnot ⟨⟨h1, h2⟩, ⟨hpcell.2.1.1.le, hpcell.2.1.2⟩, abs_le.mp h3⟩
    rw [norm_cvec_sq, hG0]
    simp

lemma integral_sliceSq_le_cellMeasure {c σ H1 L1 : ℝ} (hc : 0 < c) (hL1 : 0 ≤ L1)
    {G : Chart → Fin 2 → ℝ} (hGs : ∀ l, ContDiff ℝ ∞ (fun p => G p l))
    (hG_supp : ∀ p : Chart, G p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    IntegrableOn (sliceSq c L1 G) (Ioi 0) volume ∧
    ∫ s in Ioi 0, sliceSq c L1 G s ≤ ∫ p, ‖cvec (G p)‖ ^ 2 ∂(cellMeasure c) := by
  have hint_slice : IntegrableOn (sliceSq c L1 G) (Ioi 0) volume := by
    refine IntegrableOn.of_forall_sdiff_eq_zero (s := Icc σ H1)
      ((continuous_sliceSq c L1 hGs).continuousOn.integrableOn_compact isCompact_Icc)
      measurableSet_Ioi fun s hs => sliceSq_eq_zero_of_not_mem_Icc hG_supp hs.2
  refine ⟨hint_slice, ?_⟩
  have hslice_le : ∀ s : ℝ, sliceSq c L1 G s ≤
      ∫ x in Ioc 0 c ×ˢ (univ : Set ℝ), ‖cvec (G (s, x))‖ ^ 2 := by
    intro s
    have hcont2 : Continuous (fun x : ℝ × ℝ => ‖cvec (G (s, x))‖ ^ 2) := by
      simp_rw [norm_cvec_sq]
      have h0 : Continuous (fun x : ℝ × ℝ => G (s, x) 0) :=
        (hGs 0).continuous.comp (continuous_const.prodMk continuous_id)
      have h1 : Continuous (fun x : ℝ × ℝ => G (s, x) 1) :=
        (hGs 1).continuous.comp (continuous_const.prodMk continuous_id)
      exact (h0.pow 2).add (h1.pow 2)
    have hint_box : IntegrableOn (fun x : ℝ × ℝ => ‖cvec (G (s, x))‖ ^ 2)
        (Ioc 0 c ×ˢ Ioc (-L1) L1) := by
      have hK : IsCompact (Icc 0 c ×ˢ Icc (-L1) L1) := isCompact_Icc.prod isCompact_Icc
      exact (hcont2.continuousOn.integrableOn_compact hK).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    have hint_strip : IntegrableOn (fun x : ℝ × ℝ => ‖cvec (G (s, x))‖ ^ 2)
        (Ioc 0 c ×ˢ (univ : Set ℝ)) := by
      refine IntegrableOn.of_forall_sdiff_eq_zero (s := Icc 0 c ×ˢ Icc (-L1) L1)
        (hcont2.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
        (measurableSet_Ioc.prod MeasurableSet.univ) fun x hx => ?_
      have hG0 : G (s, x) = 0 := by
        by_contra hne
        exact hx.2 ⟨⟨hx.1.1.1.le, hx.1.1.2⟩, abs_le.mp (hG_supp (s, x) hne).2.2⟩
      rw [norm_cvec_sq, hG0]
      simp
    have heq : sliceSq c L1 G s =
        ∫ x in Ioc 0 c ×ˢ Ioc (-L1) L1, ‖cvec (G (s, x))‖ ^ 2 := by
      unfold sliceSq
      simp_rw [← norm_cvec_sq, intervalIntegral.integral_of_le hc.le,
        intervalIntegral.integral_of_le (by linarith : -L1 ≤ L1)]
      rw [Measure.volume_eq_prod, setIntegral_prod _ hint_box]
    rw [heq]
    exact setIntegral_mono_set hint_strip
      (ae_of_all _ fun _ => sq_nonneg _)
      (Eventually.of_forall fun x hx => ⟨hx.1, mem_univ _⟩)
  have hint_cell := integrableOn_cvec_sq_cell (c := c) hGs hG_supp
  have hcell_eq : cell c = Ioi 0 ×ˢ (Ioc 0 c ×ˢ (univ : Set ℝ)) := rfl
  have hprod : ∫ p in cell c, ‖cvec (G p)‖ ^ 2 =
      ∫ s in Ioi 0, ∫ x in Ioc 0 c ×ˢ (univ : Set ℝ), ‖cvec (G (s, x))‖ ^ 2 := by
    rw [hcell_eq, Measure.volume_eq_prod, setIntegral_prod _ hint_cell]
  have hint_rhs : IntegrableOn
      (fun s : ℝ => ∫ x in Ioc 0 c ×ˢ (univ : Set ℝ), ‖cvec (G (s, x))‖ ^ 2)
      (Ioi 0) volume := by
    rw [IntegrableOn, hcell_eq, Measure.volume_eq_prod,
      ← Measure.prod_restrict] at hint_cell
    exact hint_cell.integral_prod_left
  rw [cellMeasure, hprod]
  exact setIntegral_mono hint_slice hint_rhs hslice_le

/-! ### 4. Far-Field Estimate and Single-Field Weighted Moment Bound -/

/-- Far-field pointwise bound on `|lerayPot c G p|` for `L1 + 1 ≤ |p.2.2|` when `∫_cell G_1 = 0`. -/
lemma lerayPot_far_sq_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hL1 : 0 ≤ L1)
    {G : Chart → Fin 2 → ℝ} (hG : IsForceField c G)
    (hG0 : ∀ p : Chart, ∫ y in cellC c, G (p.1, p.2 - y) 1 = 0)
    (hG_supp : ∀ p : Chart, G p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    {p : Chart} (hp : L1 + 1 ≤ |p.2.2|) :
    |lerayPot c G p| ^ 2 ≤
      16 * (1 + c + c⁻¹) ^ 2 * c * L1 * sliceSq c L1 G p.1 *
        Real.exp (-(2 * cylFreq c * (|p.2.2| - L1))) := by
  have ha : 0 < cylFreq c := dd_freq_pos c hc
  set k1 : ℝ := cylFreq c / (4 * Real.pi) * Real.sign p.2.2
  have hint0 := dd_integrable c hc G hG 0 p
  have hint1 := dd_integrable c hc G hG 1 p
  have hcont1 : Continuous (fun y : ℝ × ℝ => G (p.1, p.2 - y) 1) :=
    (hG.1 1).continuous.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  have hzero : ∀ y : ℝ × ℝ, (L1 + |p.2.2|) < |y.2| → G (p.1, p.2 - y) 1 = 0 := by
    intro y hy
    have h1 := abs_sub_abs_le_abs_sub y.2 p.2.2
    have h2 : L1 < |(p.1, p.2 - y).2.2| := by
      show L1 < |p.2.2 - y.2|
      rw [abs_sub_comm]
      linarith
    have hG_eq0 : G (p.1, p.2 - y) = 0 := by
      by_contra hne
      exact absurd (hG_supp _ hne).2.2 (not_le.mpr h2)
    exact congrFun hG_eq0 1
  have hintk : Integrable (fun y : ℝ × ℝ => k1 * G (p.1, p.2 - y) 1)
      (volume.restrict (cellC c)) :=
    (rki_integrableOn_cellC _ hcont1 c (L1 + |p.2.2|) hzero).const_mul k1
  have hf : Integrable (fun y : ℝ × ℝ => cylKer c 0 y * G (p.1, p.2 - y) 0 +
      (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1))
      (volume.restrict (cellC c)) :=
    hint0.add (hint1.sub hintk)
  have hk1zero : ∫ y in cellC c, k1 * G (p.1, p.2 - y) 1 = 0 := by
    rw [MeasureTheory.integral_const_mul, hG0 p, mul_zero]
  have hsplit : lerayPot c G p = ∫ y in cellC c, (cylKer c 0 y * G (p.1, p.2 - y) 0 +
      (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1)) := by
    unfold lerayPot
    rw [Fin.sum_univ_two, ← integral_add hint0 hint1]
    have h2 : ∫ y in cellC c, (cylKer c 0 y * G (p.1, p.2 - y) 0 +
        cylKer c 1 y * G (p.1, p.2 - y) 1) =
        ∫ y in cellC c, ((cylKer c 0 y * G (p.1, p.2 - y) 0 +
          (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1)) +
          k1 * G (p.1, p.2 - y) 1) := by
      congr 1
      funext y
      ring
    rw [h2, integral_add hf hintk, hk1zero, add_zero]
  set W : Set (ℝ × ℝ) := Ioc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - L1) (p.2.2 + L1)
  have hWsub : W ⊆ cellC c := fun y hy => ⟨hy.1, mem_univ _⟩
  have hW : MeasurableSet W := measurableSet_Ioc.prod measurableSet_Icc
  set CA : ℝ := 2 * (1 + c + c⁻¹)
  have hCA0 : 0 ≤ CA := by positivity
  set E : ℝ := CA * Real.exp (-(cylFreq c * (|p.2.2| - L1)))
  have hE0 : 0 ≤ E := by positivity
  have hbound : ∀ᵐ y ∂(volume.restrict (cellC c)),
      ‖cylKer c 0 y * G (p.1, p.2 - y) 0 +
        (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1)‖ ≤
      W.indicator (fun y => E * (|G (p.1, p.2 - y) 0| + |G (p.1, p.2 - y) 1|)) y := by
    refine ae_restrict_of_forall_mem (MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ)
      fun y hy => ?_
    by_cases hyW : y ∈ W
    · rw [Set.indicator_of_mem hyW]
      have hyabs : |p.2.2| - L1 ≤ |y.2| := by
        have h1 := abs_sub_abs_le_abs_sub p.2.2 y.2
        have hy2 : |p.2.2 - y.2| ≤ L1 := abs_le.mpr ⟨by linarith [hyW.2.2], by linarith [hyW.2.1]⟩
        linarith
      have hy1 : 1 ≤ |y.2| := by linarith
      have hsign : Real.sign y.2 = Real.sign p.2.2 := by
        rcases le_total 0 p.2.2 with h0 | h0
        · rw [abs_of_nonneg h0] at hp
          have hyp : 0 < y.2 := by linarith [hyW.2.1]
          rw [Real.sign_of_pos hyp, Real.sign_of_pos (by linarith)]
        · rw [abs_of_nonpos h0] at hp
          have hyn : y.2 < 0 := by linarith [hyW.2.2]
          rw [Real.sign_of_neg hyn, Real.sign_of_neg (by linarith)]
      obtain ⟨hA0, hA1⟩ := cylKerAsym_explicit hc hy1
      rw [hsign] at hA1
      have hexp : Real.exp (-(cylFreq c * |y.2|)) ≤
          Real.exp (-(cylFreq c * (|p.2.2| - L1))) :=
        Real.exp_le_exp.mpr (by have := mul_le_mul_of_nonneg_left hyabs ha.le; linarith)
      have hK0 : |cylKer c 0 y| ≤ E :=
        hA0.trans (mul_le_mul_of_nonneg_left hexp hCA0)
      have hK1 : |cylKer c 1 y - k1| ≤ E :=
        hA1.trans (mul_le_mul_of_nonneg_left hexp hCA0)
      calc ‖cylKer c 0 y * G (p.1, p.2 - y) 0 +
            (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1)‖
          = |cylKer c 0 y * G (p.1, p.2 - y) 0 +
            (cylKer c 1 y - k1) * G (p.1, p.2 - y) 1| := by
            rw [Real.norm_eq_abs]
            congr 1
            ring
        _ ≤ |cylKer c 0 y * G (p.1, p.2 - y) 0| +
            |(cylKer c 1 y - k1) * G (p.1, p.2 - y) 1| := abs_add_le _ _
        _ = |cylKer c 0 y| * |G (p.1, p.2 - y) 0| +
            |cylKer c 1 y - k1| * |G (p.1, p.2 - y) 1| := by rw [abs_mul, abs_mul]
        _ ≤ E * |G (p.1, p.2 - y) 0| + E * |G (p.1, p.2 - y) 1| :=
            add_le_add (mul_le_mul_of_nonneg_right hK0 (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hK1 (abs_nonneg _))
        _ = E * (|G (p.1, p.2 - y) 0| + |G (p.1, p.2 - y) 1|) := by ring
    · rw [Set.indicator_of_notMem hyW]
      have hyS : L1 < |p.2.2 - y.2| := by
        by_contra hcon
        rw [not_lt] at hcon
        apply hyW
        exact ⟨hy.1, ⟨by linarith [(abs_le.mp hcon).2], by linarith [(abs_le.mp hcon).1]⟩⟩
      have hz : G (p.1, p.2 - y) = 0 := by
        by_contra hne
        exact absurd (hG_supp (p.1, p.2 - y) hne).2.2 (not_le.mpr hyS)
      rw [hz]
      simp
  have hcont_sum : Continuous (fun x : ℝ × ℝ => |G (p.1, x) 0| + |G (p.1, x) 1|) := by
    have h0 : Continuous (fun x : ℝ × ℝ => G (p.1, x) 0) :=
      (hG.1 0).continuous.comp (continuous_const.prodMk continuous_id)
    have h1 : Continuous (fun x : ℝ × ℝ => G (p.1, x) 1) :=
      (hG.1 1).continuous.comp (continuous_const.prodMk continuous_id)
    exact h0.abs.add h1.abs
  have hgW_int : IntegrableOn
      (fun y : ℝ × ℝ => E * (|G (p.1, p.2 - y) 0| + |G (p.1, p.2 - y) 1|)) W := by
    have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - L1) (p.2.2 + L1)) :=
      isCompact_Icc.prod isCompact_Icc
    have hcW : Continuous (fun y : ℝ × ℝ =>
        E * (|G (p.1, p.2 - y) 0| + |G (p.1, p.2 - y) 1|)) :=
      continuous_const.mul (hcont_sum.comp (continuous_const.sub continuous_id))
    exact (hcW.continuousOn.integrableOn_compact hK).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)
  have hgint : Integrable
      (W.indicator (fun y => E * (|G (p.1, p.2 - y) 0| + |G (p.1, p.2 - y) 1|)))
      (volume.restrict (cellC c)) := by
    rw [integrable_indicator_iff hW]
    show IntegrableOn _ W (volume.restrict (cellC c))
    rw [IntegrableOn, Measure.restrict_restrict hW, inter_eq_left.mpr hWsub]
    exact hgW_int
  have hle_int := norm_integral_le_of_norm_le hgint hbound
  have hind_eq : ∫ y in cellC c,
      W.indicator (fun y => E * (|G (p.1, p.2 - y) 0| + |G (p.1, p.2 - y) 1|)) y =
      E * ∫ q in (0 : ℝ)..c, ∫ η in (-L1)..L1, (|G (p.1, q, η) 0| + |G (p.1, q, η) 1|) := by
    rw [MeasureTheory.integral_indicator hW, Measure.restrict_restrict hW, inter_eq_left.mpr hWsub,
      MeasureTheory.integral_const_mul]
    congr 1
    exact window_shift_eq hc hL1 hcont_sum
      (fun q η => by simp [congrFun (hG.2.1 p.1 q η) 0, congrFun (hG.2.1 p.1 q η) 1]) p.2
  have hpot_le : |lerayPot c G p| ≤
      E * ∫ q in (0 : ℝ)..c, ∫ η in (-L1)..L1, (|G (p.1, q, η) 0| + |G (p.1, q, η) 1|) := by
    rw [hsplit, ← Real.norm_eq_abs]
    exact hle_int.trans hind_eq.le
  have hpot_sq : |lerayPot c G p| ^ 2 ≤
      E ^ 2 * (∫ q in (0 : ℝ)..c, ∫ η in (-L1)..L1, (|G (p.1, q, η) 0| + |G (p.1, q, η) 1|)) ^ 2 := by
    calc |lerayPot c G p| ^ 2
        ≤ (E * ∫ q in (0 : ℝ)..c, ∫ η in (-L1)..L1, (|G (p.1, q, η) 0| + |G (p.1, q, η) 1|)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hpot_le 2
      _ = E ^ 2 *
          (∫ q in (0 : ℝ)..c, ∫ η in (-L1)..L1, (|G (p.1, q, η) 0| + |G (p.1, q, η) 1|)) ^ 2 :=
          mul_pow _ _ 2
  have hE_sq : E ^ 2 = 4 * (1 + c + c⁻¹) ^ 2 * Real.exp (-(2 * cylFreq c * (|p.2.2| - L1))) := by
    dsimp only [E, CA]
    rw [mul_pow, mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 1
    · norm_num
    · congr 1
      ring
  calc |lerayPot c G p| ^ 2
      ≤ E ^ 2 * (4 * c * L1 * sliceSq c L1 G p.1) :=
        hpot_sq.trans (mul_le_mul_of_nonneg_left (gSlice_sq_le_sliceSq hc hL1 hG.1 p.1) (sq_nonneg E))
    _ = 16 * (1 + c + c⁻¹) ^ 2 * c * L1 * sliceSq c L1 G p.1 *
          Real.exp (-(2 * cylFreq c * (|p.2.2| - L1))) := by
        rw [hE_sq]
        ring

/-- Far-field `η` weight bound against `(1 + η ^ 2)⁻¹` for `L1 + 1 ≤ |η|` and `j < 3`. -/
lemma far_eta_weight_le {c L1 : ℝ} (hc : 0 < c) (hL1 : 0 ≤ L1) {j : ℕ} (hj : j < 3)
    {η : ℝ} (hη : L1 + 1 ≤ |η|) :
    (|η| ^ j) ^ 2 * Real.exp (-(2 * cylFreq c * (|η| - L1))) ≤
      2 * (1 + L1) ^ 6 * c ^ 6 * (1 + η ^ 2)⁻¹ := by
  set d : ℝ := |η| - L1
  have hd1 : 1 ≤ d := by change 1 ≤ |η| - L1; linarith
  have hd0 : 0 ≤ d := zero_le_one.trans hd1
  have hη1 : 1 ≤ |η| := by linarith
  have hη0 : 0 ≤ |η| := abs_nonneg η
  have hη_le : |η| ≤ (1 + L1) * d := by
    change |η| ≤ (1 + L1) * (|η| - L1)
    nlinarith
  have hj_le : |η| ^ j ≤ |η| ^ 2 := by
    interval_cases j
    · simp
      nlinarith
    · nlinarith
    · rfl
  have hj_sq : (|η| ^ j) ^ 2 ≤ |η| ^ 4 := by
    calc (|η| ^ j) ^ 2 ≤ (|η| ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hj_le 2
      _ = |η| ^ 4 := by ring
  have h1η : 1 + η ^ 2 ≤ 2 * |η| ^ 2 := by
    have : 1 ≤ |η| ^ 2 := by nlinarith
    nlinarith [sq_abs η]
  have hpoly : (1 + η ^ 2) * (|η| ^ j) ^ 2 ≤ 2 * (1 + L1) ^ 6 * d ^ 6 := by
    have h6 : |η| ^ 6 ≤ ((1 + L1) * d) ^ 6 := pow_le_pow_left₀ hη0 hη_le 6
    calc (1 + η ^ 2) * (|η| ^ j) ^ 2
        ≤ (2 * |η| ^ 2) * |η| ^ 4 :=
          mul_le_mul h1η hj_sq (sq_nonneg _) (by positivity)
      _ = 2 * |η| ^ 6 := by ring
      _ ≤ 2 * ((1 + L1) * d) ^ 6 := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = 2 * (1 + L1) ^ 6 * d ^ 6 := by ring
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ha6 : c⁻¹ ≤ 2 * cylFreq c / 6 := by
    unfold cylFreq
    rw [inv_eq_one_div, mul_div_assoc', div_div, div_le_div_iff₀ hc (by positivity)]
    nlinarith
  have hexp1 : c⁻¹ * d ≤ Real.exp (2 * cylFreq c / 6 * d) := by
    have h1 : c⁻¹ * d ≤ 2 * cylFreq c / 6 * d := mul_le_mul_of_nonneg_right ha6 hd0
    have h2 : 2 * cylFreq c / 6 * d ≤ 2 * cylFreq c / 6 * d + 1 := by linarith
    exact (h1.trans h2).trans (Real.add_one_le_exp _)
  have hexp6 : (c⁻¹ * d) ^ 6 ≤ Real.exp (2 * cylFreq c * d) := by
    calc (c⁻¹ * d) ^ 6
        ≤ (Real.exp (2 * cylFreq c / 6 * d)) ^ 6 :=
          pow_le_pow_left₀ (by positivity) hexp1 6
      _ = Real.exp ((6 : ℕ) * (2 * cylFreq c / 6 * d)) := (Real.exp_nat_mul _ 6).symm
      _ = Real.exp (2 * cylFreq c * d) := by
          congr 1
          push_cast
          ring
  have hd6_exp : d ^ 6 * Real.exp (-(2 * cylFreq c * d)) ≤ c ^ 6 := by
    have hcc : c ^ 6 * (c⁻¹ * d) ^ 6 = d ^ 6 := by
      rw [mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow, one_mul]
    calc d ^ 6 * Real.exp (-(2 * cylFreq c * d))
        = c ^ 6 * (c⁻¹ * d) ^ 6 * Real.exp (-(2 * cylFreq c * d)) := by rw [hcc]
      _ ≤ c ^ 6 * Real.exp (2 * cylFreq c * d) * Real.exp (-(2 * cylFreq c * d)) := by
          gcongr
      _ = c ^ 6 * (Real.exp (2 * cylFreq c * d) * Real.exp (-(2 * cylFreq c * d))) := by ring
      _ = c ^ 6 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have htot : (1 + η ^ 2) * ((|η| ^ j) ^ 2 * Real.exp (-(2 * cylFreq c * d))) ≤
      2 * (1 + L1) ^ 6 * c ^ 6 := by
    calc (1 + η ^ 2) * ((|η| ^ j) ^ 2 * Real.exp (-(2 * cylFreq c * d)))
        = ((1 + η ^ 2) * (|η| ^ j) ^ 2) * Real.exp (-(2 * cylFreq c * d)) := by ring
      _ ≤ (2 * (1 + L1) ^ 6 * d ^ 6) * Real.exp (-(2 * cylFreq c * d)) :=
          mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
      _ = 2 * (1 + L1) ^ 6 * (d ^ 6 * Real.exp (-(2 * cylFreq c * d))) := by ring
      _ ≤ 2 * (1 + L1) ^ 6 * c ^ 6 :=
          mul_le_mul_of_nonneg_left hd6_exp (by positivity)
  have hpos : 0 < 1 + η ^ 2 := by positivity
  calc (|η| ^ j) ^ 2 * Real.exp (-(2 * cylFreq c * d))
      = (1 + η ^ 2)⁻¹ * ((1 + η ^ 2) * ((|η| ^ j) ^ 2 * Real.exp (-(2 * cylFreq c * d)))) := by
        rw [inv_mul_cancel_left₀ hpos.ne']
    _ ≤ (1 + η ^ 2)⁻¹ * (2 * (1 + L1) ^ 6 * c ^ 6) :=
        mul_le_mul_of_nonneg_left htot (inv_nonneg.mpr hpos.le)
    _ = 2 * (1 + L1) ^ 6 * c ^ 6 * (1 + η ^ 2)⁻¹ := by ring

/-- Integrability and integral bound for `p ↦ sliceSq c L1 G p.1 * (1 + p.2.2 ^ 2)⁻¹` on `measureH c`. -/
lemma integrable_and_integral_sliceSq_inv_one_add_sq_le {c σ H1 L1 : ℝ}
    (hc : 0 < c) (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    {G : Chart → Fin 2 → ℝ} (hGs : ∀ l, ContDiff ℝ ∞ (fun p => G p l))
    (hG_supp : ∀ p : Chart, G p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    Integrable (fun p : Chart => sliceSq c L1 G p.1 * (1 + p.2.2 ^ 2)⁻¹) (measureH c) ∧
    ∫ p, sliceSq c L1 G p.1 * (1 + p.2.2 ^ 2)⁻¹ ∂(measureH c) ≤
      4 * c * (1 + σ⁻¹ + H1 + L1) ^ 2 * ∫ p, ‖cvec (G p)‖ ^ 2 ∂(cellMeasure c) := by
  set φ : ℝ → ℝ := fun s => s ^ (-(3 / 2 : ℝ)) * sliceSq c L1 G s
  have hφ_int : Integrable φ (volume.restrict (Ioi 0)) := by
    show IntegrableOn φ (Ioi 0) volume
    refine IntegrableOn.of_forall_sdiff_eq_zero (s := Icc σ H1) ?_
      measurableSet_Ioi fun s hs => ?_
    · refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
      refine ContinuousOn.mul ?_ (continuous_sliceSq c L1 hGs).continuousOn
      refine ContinuousOn.rpow_const continuous_id.continuousOn fun s hs => Or.inl ?_
      have : σ ≤ s := hs.1
      linarith
    · simp [φ, sliceSq_eq_zero_of_not_mem_Icc hG_supp hs.2]
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 c)) :=
    integrableOn_const (by simp)
  have h2 : Integrable (fun η : ℝ => (1 + η ^ 2)⁻¹) (volume.restrict (univ : Set ℝ)) := by
    rw [Measure.restrict_univ]
    exact integrable_inv_one_add_sq
  have h12 : Integrable (fun x : ℝ × ℝ => (1 : ℝ) * (1 + x.2 ^ 2)⁻¹)
      (volume.restrict (Ioc 0 c ×ˢ (univ : Set ℝ))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact h1.mul_prod h2
  have hprod : Integrable (fun p : Chart => φ p.1 * ((1 : ℝ) * (1 + p.2.2 ^ 2)⁻¹))
      (cellMeasure c) := by
    unfold cellMeasure
    have hcell_eq : cell c = Ioi 0 ×ˢ (Ioc 0 c ×ˢ (univ : Set ℝ)) := rfl
    rw [hcell_eq, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hφ_int.mul_prod h12
  have hint_H : Integrable (fun p : Chart => sliceSq c L1 G p.1 * (1 + p.2.2 ^ 2)⁻¹)
      (measureH c) := by
    rw [measureH, integrable_withDensity_iff_integrable_smul' measurable_weightH
      (ae_weightH_lt_top c)]
    refine hprod.congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p hp
    have hp1 : 0 < p.1 := hp.1
    simp only [weightH, ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _), smul_eq_mul, φ]
    ring
  refine ⟨hint_H, ?_⟩
  have hrew : ∫ p, sliceSq c L1 G p.1 * (1 + p.2.2 ^ 2)⁻¹ ∂(measureH c) =
      ∫ p in cell c, φ p.1 * ((1 : ℝ) * (1 + p.2.2 ^ 2)⁻¹) := by
    rw [measureH, integral_withDensity_eq_integral_toReal_smul measurable_weightH
      (ae_weightH_lt_top c), cellMeasure]
    refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    simp only [weightH, ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _), smul_eq_mul, φ]
    ring
  have hfact1 : ∫ p in cell c, φ p.1 * ((1 : ℝ) * (1 + p.2.2 ^ 2)⁻¹) =
      (∫ s in Ioi 0, φ s) * (∫ x in Ioc 0 c ×ˢ (univ : Set ℝ), (1 : ℝ) * (1 + x.2 ^ 2)⁻¹) := by
    have hcell_eq : cell c = Ioi 0 ×ˢ (Ioc 0 c ×ˢ (univ : Set ℝ)) := rfl
    rw [hcell_eq, Measure.volume_eq_prod,
      setIntegral_prod_mul (f := φ) (g := fun x : ℝ × ℝ => (1 : ℝ) * (1 + x.2 ^ 2)⁻¹)]
  have hfact2 : ∫ x in Ioc 0 c ×ˢ (univ : Set ℝ), (1 : ℝ) * (1 + x.2 ^ 2)⁻¹ = c * Real.pi := by
    rw [Measure.volume_eq_prod,
      setIntegral_prod_mul (f := fun _ : ℝ => (1 : ℝ)) (g := fun η : ℝ => (1 + η ^ 2)⁻¹)]
    have hq : ∫ _ in Ioc 0 c, (1 : ℝ) = c := by
      simp [sub_zero, hc.le]
    have hη : ∫ η in (univ : Set ℝ), (1 + η ^ 2)⁻¹ = Real.pi := by
      rw [Measure.restrict_univ, integral_univ_inv_one_add_sq]
    rw [hq, hη]
  obtain ⟨hslice_int, hslice_le⟩ := integral_sliceSq_le_cellMeasure hc hL1 hGs hG_supp
  set A : ℝ := 1 + σ⁻¹ + H1 + L1
  have hφ_le : ∀ s : ℝ, φ s ≤ A ^ 2 * sliceSq c L1 G s := by
    intro s
    by_cases hs : s ∈ Icc σ H1
    · exact mul_le_mul_of_nonneg_right
        (ObsBoxS1Aux.rpow_neg_three_halves_le hσ hσH1 hL1 hs.1)
        (sliceSq_nonneg hc hL1 G s)
    · simp [φ, sliceSq_eq_zero_of_not_mem_Icc hG_supp hs]
  have hφ_int_le : ∫ s in Ioi 0, φ s ≤ A ^ 2 * ∫ p, ‖cvec (G p)‖ ^ 2 ∂(cellMeasure c) := by
    have hmono := setIntegral_mono hφ_int (hslice_int.const_mul (A ^ 2)) hφ_le
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hslice_le (sq_nonneg A))
  have hφ_nonneg : 0 ≤ ∫ s in Ioi 0, φ s :=
    setIntegral_nonneg measurableSet_Ioi fun s hs =>
      mul_nonneg (Real.rpow_nonneg hs.le _) (sliceSq_nonneg hc hL1 G s)
  have hcpi_le : c * Real.pi ≤ 4 * c := by nlinarith [Real.pi_le_four]
  rw [hrew, hfact1, hfact2]
  calc (∫ s in Ioi 0, φ s) * (c * Real.pi)
      ≤ (A ^ 2 * ∫ p, ‖cvec (G p)‖ ^ 2 ∂(cellMeasure c)) * (4 * c) :=
        mul_le_mul hφ_int_le hcpi_le (by positivity)
          (mul_nonneg (sq_nonneg A) (integral_nonneg fun _ => sq_nonneg _))
    _ = 4 * c * A ^ 2 * ∫ p, ‖cvec (G p)‖ ^ 2 ∂(cellMeasure c) := by ring

/-- Bound `∫ p, ‖cvec (F p)‖ ^ 2 ∂(measureH c)` by `(1 + σ⁻¹ + H1 + L1) ^ 2 * ∫ p, ‖cvec (F p)‖ ^ 2 ∂(cellMeasure c)`. -/
lemma integral_cvec_measureH_le {c σ H1 L1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    {F : Chart → Fin 2 → ℝ} (hFs : ∀ l, ContDiff ℝ ∞ (fun p => F p l))
    (hF_supp : ∀ p : Chart, F p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    ∫ p, ‖cvec (F p)‖ ^ 2 ∂(measureH c) ≤
      (1 + σ⁻¹ + H1 + L1) ^ 2 * ∫ p, ‖cvec (F p)‖ ^ 2 ∂(cellMeasure c) := by
  set A : ℝ := 1 + σ⁻¹ + H1 + L1
  have hrew : ∫ p, ‖cvec (F p)‖ ^ 2 ∂(measureH c) =
      ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * ‖cvec (F p)‖ ^ 2 := by
    rw [measureH, integral_withDensity_eq_integral_toReal_smul measurable_weightH
      (ae_weightH_lt_top c), cellMeasure]
    refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    simp only [weightH, ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _), smul_eq_mul]
  have hint_cell := integrableOn_cvec_sq_cell (c := c) hFs hF_supp
  rw [hrew, cellMeasure, ← MeasureTheory.integral_const_mul]
  refine integral_mono_of_nonneg ?_ (hint_cell.const_mul (A ^ 2)) ?_
  · filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p hp
    exact mul_nonneg (Real.rpow_nonneg hp.1.le _) (sq_nonneg _)
  · filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p _
    by_cases hne : F p = 0
    · rw [norm_cvec_sq, hne]
      simp
    · exact mul_le_mul_of_nonneg_right
        (ObsBoxS1Aux.rpow_neg_three_halves_le hσ hσH1 hL1 (hF_supp p hne).1)
        (sq_nonneg _)

/-- `dfDv F u` inherits support in `dtdBand σ H1 L1` from `F`. -/
lemma dfDv_supp_of_supp {σ H1 L1 : ℝ} {F : Chart → Fin 2 → ℝ} (u : Chart)
    (hF_supp : ∀ p : Chart, F p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    ∀ p : Chart, dfDv F u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  intro p hp
  by_contra hnot
  have hev : ∀ l : Fin 2, (fun q => F q l) =ᶠ[nhds p] fun _ => (0 : ℝ) := by
    intro l
    filter_upwards [(dtdBand_closed σ H1 L1).isOpen_compl.mem_nhds hnot] with q hq
    by_contra hne
    exact hq (hF_supp q fun h0 => hne (congrFun h0 l))
  apply hp
  ext l
  show fderiv ℝ (fun q => F q l) p u = 0
  rw [(hev l).fderiv_eq]
  simp

lemma box_coeff_bounds {c σ H1 L1 Γ : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    (h1Γ : 1 ≤ Γ) (hc_Γ : 1 + c + c⁻¹ ≤ Γ) (hA_Γ : 1 + σ⁻¹ + H1 + L1 ≤ Γ) :
    (1 + L1) ^ 4 * (1 + σ⁻¹ + H1 + L1) ^ 2 ≤ (16 * Γ ^ 10) ^ 2 ∧
    (32 * (1 + c + c⁻¹) ^ 2 * c ^ 7 * L1 * (1 + L1) ^ 6) *
      (4 * c * (1 + σ⁻¹ + H1 + L1) ^ 2) ≤ (16 * Γ ^ 10) ^ 2 := by
  have hH1 : 0 ≤ H1 := hσ.le.trans hσH1
  have hσ_inv : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have hc_inv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hΓ0 : 0 ≤ Γ := zero_le_one.trans h1Γ
  have h1L1_Γ : 1 + L1 ≤ Γ := by linarith
  have hL1_Γ : L1 ≤ Γ := by linarith
  have hc_le_Γ : c ≤ Γ := by linarith
  refine ⟨?_, ?_⟩
  · have h1 : (1 + L1) ^ 4 ≤ Γ ^ 4 := pow_le_pow_left₀ (by positivity) h1L1_Γ 4
    have h2 : (1 + σ⁻¹ + H1 + L1) ^ 2 ≤ Γ ^ 2 := pow_le_pow_left₀ (by positivity) hA_Γ 2
    have h3 : Γ ^ 6 ≤ Γ ^ 20 := pow_le_pow_right₀ h1Γ (by omega)
    calc (1 + L1) ^ 4 * (1 + σ⁻¹ + H1 + L1) ^ 2
        ≤ Γ ^ 4 * Γ ^ 2 := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = Γ ^ 6 := by ring
      _ ≤ Γ ^ 20 := h3
      _ ≤ 256 * Γ ^ 20 := le_mul_of_one_le_left (by positivity) (by norm_num)
      _ = (16 * Γ ^ 10) ^ 2 := by ring
  · have h1 : (1 + c + c⁻¹) ^ 2 ≤ Γ ^ 2 := pow_le_pow_left₀ (by positivity) hc_Γ 2
    have h2 : c ^ 8 ≤ Γ ^ 8 := pow_le_pow_left₀ hc.le hc_le_Γ 8
    have h3 : (1 + L1) ^ 6 ≤ Γ ^ 6 := pow_le_pow_left₀ (by positivity) h1L1_Γ 6
    have h4 : (1 + σ⁻¹ + H1 + L1) ^ 2 ≤ Γ ^ 2 := pow_le_pow_left₀ (by positivity) hA_Γ 2
    have hprod1 : (1 + c + c⁻¹) ^ 2 * c ^ 8 ≤ Γ ^ 2 * Γ ^ 8 :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have hprod2 : L1 * (1 + L1) ^ 6 ≤ Γ * Γ ^ 6 :=
      mul_le_mul hL1_Γ h3 (by positivity) hΓ0
    have hprod3 : ((1 + c + c⁻¹) ^ 2 * c ^ 8) * (L1 * (1 + L1) ^ 6) ≤
        (Γ ^ 2 * Γ ^ 8) * (Γ * Γ ^ 6) :=
      mul_le_mul hprod1 hprod2 (by positivity) (by positivity)
    have hprod4 : (((1 + c + c⁻¹) ^ 2 * c ^ 8) * (L1 * (1 + L1) ^ 6)) *
        (1 + σ⁻¹ + H1 + L1) ^ 2 ≤
        ((Γ ^ 2 * Γ ^ 8) * (Γ * Γ ^ 6)) * Γ ^ 2 :=
      mul_le_mul hprod3 h4 (by positivity) (by positivity)
    have h19 : Γ ^ 19 ≤ Γ ^ 20 := pow_le_pow_right₀ h1Γ (by omega)
    calc (32 * (1 + c + c⁻¹) ^ 2 * c ^ 7 * L1 * (1 + L1) ^ 6) *
          (4 * c * (1 + σ⁻¹ + H1 + L1) ^ 2)
        = 128 * ((((1 + c + c⁻¹) ^ 2 * c ^ 8) * (L1 * (1 + L1) ^ 6)) *
            (1 + σ⁻¹ + H1 + L1) ^ 2) := by ring
      _ ≤ 128 * (((Γ ^ 2 * Γ ^ 8) * (Γ * Γ ^ 6)) * Γ ^ 2) :=
          mul_le_mul_of_nonneg_left hprod4 (by norm_num)
      _ = 128 * Γ ^ 19 := by ring
      _ ≤ 128 * Γ ^ 20 := mul_le_mul_of_nonneg_left h19 (by norm_num)
      _ ≤ 256 * Γ ^ 20 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (16 * Γ ^ 10) ^ 2 := by ring

/-- Combined near + far bound on `∫ p, (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c F p)‖ ^ 2 ∂(measureH c)`. -/
lemma integral_weighted_lerayField_sq_le {c σ H1 L1 Γ : ℝ}
    (hc : 0 < c) (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    (h1Γ : 1 ≤ Γ) (hc_Γ : 1 + c + c⁻¹ ≤ Γ) (hA_Γ : 1 + σ⁻¹ + H1 + L1 ≤ Γ)
    {F : Chart → Fin 2 → ℝ} (hF : IsForceField c F)
    (hF_supp : ∀ p : Chart, F p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    {j : ℕ} (hj : j < 3) :
    Integrable (fun p : Chart => (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c F p)‖ ^ 2) (measureH c) ∧
    ∫ p, (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c F p)‖ ^ 2 ∂(measureH c) ≤
      (16 * Γ ^ 10) ^ 2 *
        (∫ p, ‖cvec (F p)‖ ^ 2 ∂(cellMeasure c) +
          ∫ p, ‖cvec (dfDv F (lfpDir 0) p)‖ ^ 2 ∂(cellMeasure c) +
          ∫ p, ‖cvec (dfDv F (lfpDir 1) p)‖ ^ 2 ∂(cellMeasure c)) := by
  set G0 : Chart → Fin 2 → ℝ := dfDv F (lfpDir 0)
  set G1 : Chart → Fin 2 → ℝ := dfDv F (lfpDir 1)
  have hG0 : IsForceField c G0 := forceFieldDeriv c F hF (lfpDir 0)
  have hG1 : IsForceField c G1 := forceFieldDeriv c F hF (lfpDir 1)
  have hG0_zero : ∀ p : Chart, ∫ y in cellC c, G0 (p.1, p.2 - y) 1 = 0 :=
    fun p => dd_int_zero c hc F hF p 0
  have hG1_zero : ∀ p : Chart, ∫ y in cellC c, G1 (p.1, p.2 - y) 1 = 0 :=
    fun p => dd_int_zero c hc F hF p 1
  have hG0_supp := dfDv_supp_of_supp (lfpDir 0) hF_supp
  have hG1_supp := dfDv_supp_of_supp (lfpDir 1) hF_supp
  set K : ℝ := 32 * (1 + c + c⁻¹) ^ 2 * c ^ 7 * L1 * (1 + L1) ^ 6
  have hK0 : 0 ≤ K := by positivity
  set gF : Chart → ℝ := fun p => (1 + L1) ^ 4 * ‖cvec (lerayField c F p)‖ ^ 2
  set g0 : Chart → ℝ := fun p => K * (sliceSq c L1 G0 p.1 * (1 + p.2.2 ^ 2)⁻¹)
  set g1 : Chart → ℝ := fun p => K * (sliceSq c L1 G1 p.1 * (1 + p.2.2 ^ 2)⁻¹)
  have hpt : ∀ p : Chart,
      (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c F p)‖ ^ 2 ≤ gF p + g0 p + g1 p := by
    intro p
    have hfar0_nn : 0 ≤ g0 p :=
      mul_nonneg hK0 (mul_nonneg (sliceSq_nonneg hc hL1 G0 p.1) (by positivity))
    have hfar1_nn : 0 ≤ g1 p :=
      mul_nonneg hK0 (mul_nonneg (sliceSq_nonneg hc hL1 G1 p.1) (by positivity))
    rcases lt_or_ge |p.2.2| (L1 + 1) with hnear | hfar
    · have hj_le : |p.2.2| ^ j ≤ (1 + L1) ^ 2 := by
        have h1 : |p.2.2| ≤ 1 + L1 := by linarith
        interval_cases j
        · rw [pow_zero]
          nlinarith
        · nlinarith [abs_nonneg p.2.2]
        · exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hj_sq : (|p.2.2| ^ j) ^ 2 ≤ (1 + L1) ^ 4 := by
        calc (|p.2.2| ^ j) ^ 2 ≤ ((1 + L1) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hj_le 2
          _ = (1 + L1) ^ 4 := by ring
      have h1 : (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c F p)‖ ^ 2 ≤ gF p :=
        mul_le_mul_of_nonneg_right hj_sq (sq_nonneg _)
      linarith
    · have hFp0 : F p = 0 := by
        by_contra hne
        have := (hF_supp p hne).2.2
        linarith
      have hLF : ‖cvec (lerayField c F p)‖ ^ 2 =
          |lerayPot c G0 p| ^ 2 + |lerayPot c G1 p| ^ 2 := by
        rw [norm_cvec_sq]
        have hgrad0 : flatGrad (lerayPot c F) p 0 = lerayPot c G0 p :=
          (lerayPotSmooth c hc F hF).2.2 p (lfpDir 0)
        have hgrad1 : flatGrad (lerayPot c F) p 1 = lerayPot c G1 p :=
          (lerayPotSmooth c hc F hF).2.2 p (lfpDir 1)
        have h0 : lerayField c F p 0 = -lerayPot c G0 p := by
          show F p 0 - flatGrad (lerayPot c F) p 0 = -lerayPot c G0 p
          rw [hFp0, Pi.zero_apply, zero_sub, hgrad0]
        have h1 : lerayField c F p 1 = -lerayPot c G1 p := by
          show F p 1 - flatGrad (lerayPot c F) p 1 = -lerayPot c G1 p
          rw [hFp0, Pi.zero_apply, zero_sub, hgrad1]
        rw [h0, h1, neg_sq, neg_sq, sq_abs, sq_abs]
      have hpot0 := lerayPot_far_sq_le hc hL1 hG0 hG0_zero hG0_supp hfar
      have hpot1 := lerayPot_far_sq_le hc hL1 hG1 hG1_zero hG1_supp hfar
      have heta := far_eta_weight_le hc hL1 hj hfar
      have hb0 : (|p.2.2| ^ j) ^ 2 * |lerayPot c G0 p| ^ 2 ≤ g0 p := by
        calc (|p.2.2| ^ j) ^ 2 * |lerayPot c G0 p| ^ 2
            ≤ (|p.2.2| ^ j) ^ 2 * (16 * (1 + c + c⁻¹) ^ 2 * c * L1 * sliceSq c L1 G0 p.1 *
                Real.exp (-(2 * cylFreq c * (|p.2.2| - L1)))) :=
              mul_le_mul_of_nonneg_left hpot0 (sq_nonneg _)
          _ = 16 * (1 + c + c⁻¹) ^ 2 * c * L1 * sliceSq c L1 G0 p.1 *
                ((|p.2.2| ^ j) ^ 2 * Real.exp (-(2 * cylFreq c * (|p.2.2| - L1)))) := by ring
          _ ≤ 16 * (1 + c + c⁻¹) ^ 2 * c * L1 * sliceSq c L1 G0 p.1 *
                (2 * (1 + L1) ^ 6 * c ^ 6 * (1 + p.2.2 ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left heta
                (mul_nonneg (by positivity) (sliceSq_nonneg hc hL1 G0 p.1))
          _ = g0 p := by
              dsimp only [g0, K]
              ring
      have hb1 : (|p.2.2| ^ j) ^ 2 * |lerayPot c G1 p| ^ 2 ≤ g1 p := by
        calc (|p.2.2| ^ j) ^ 2 * |lerayPot c G1 p| ^ 2
            ≤ (|p.2.2| ^ j) ^ 2 * (16 * (1 + c + c⁻¹) ^ 2 * c * L1 * sliceSq c L1 G1 p.1 *
                Real.exp (-(2 * cylFreq c * (|p.2.2| - L1)))) :=
              mul_le_mul_of_nonneg_left hpot1 (sq_nonneg _)
          _ = 16 * (1 + c + c⁻¹) ^ 2 * c * L1 * sliceSq c L1 G1 p.1 *
                ((|p.2.2| ^ j) ^ 2 * Real.exp (-(2 * cylFreq c * (|p.2.2| - L1)))) := by ring
          _ ≤ 16 * (1 + c + c⁻¹) ^ 2 * c * L1 * sliceSq c L1 G1 p.1 *
                (2 * (1 + L1) ^ 6 * c ^ 6 * (1 + p.2.2 ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left heta
                (mul_nonneg (by positivity) (sliceSq_nonneg hc hL1 G1 p.1))
          _ = g1 p := by
              dsimp only [g1, K]
              ring
      have hnear_nn : 0 ≤ gF p := by dsimp only [gF]; positivity
      rw [hLF, mul_add]
      linarith
  obtain ⟨hiF, _, hleF⟩ := integral_cvec_lerayField_sq_le hc hF
  obtain ⟨hiG0, hleG0⟩ := integrable_and_integral_sliceSq_inv_one_add_sq_le hc hσ hσH1 hL1
    hG0.1 hG0_supp
  obtain ⟨hiG1, hleG1⟩ := integrable_and_integral_sliceSq_inv_one_add_sq_le hc hσ hσH1 hL1
    hG1.1 hG1_supp
  have higF : Integrable gF (measureH c) := hiF.const_mul ((1 + L1) ^ 4)
  have hig0 : Integrable g0 (measureH c) := hiG0.const_mul K
  have hig1 : Integrable g1 (measureH c) := hiG1.const_mul K
  have hig01 : Integrable (fun p => gF p + g0 p) (measureH c) := higF.add hig0
  have hi_rhs : Integrable (fun p => (gF p + g0 p) + g1 p) (measureH c) :=
    hig01.add hig1
  have hi_lhs : Integrable
      (fun p : Chart => (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c F p)‖ ^ 2) (measureH c) := by
    have hcont : Continuous
        (fun p : Chart => (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c F p)‖ ^ 2) := by
      simp_rw [norm_cvec_sq]
      have h0 : Continuous (fun p : Chart => lerayField c F p 0) :=
        ((lerayFieldProps c hc F hF).1 0).continuous
      have h1 : Continuous (fun p : Chart => lerayField c F p 1) :=
        ((lerayFieldProps c hc F hF).1 1).continuous
      have hjc : Continuous (fun p : Chart => (|p.2.2| ^ j) ^ 2) := by fun_prop
      exact hjc.mul ((h0.pow 2).add (h1.pow 2))
    refine hi_rhs.mono' hcont.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpt p
  refine ⟨hi_lhs, ?_⟩
  have hmono := integral_mono_of_nonneg
    (ae_of_all _ fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    hi_rhs (ae_of_all _ hpt)
  rw [integral_add hig01 hig1, integral_add higF hig0] at hmono
  have hgF_eq : ∫ p, gF p ∂(measureH c) =
      (1 + L1) ^ 4 * ∫ p, ‖cvec (lerayField c F p)‖ ^ 2 ∂(measureH c) :=
    MeasureTheory.integral_const_mul _ _
  have hg0_eq : ∫ p, g0 p ∂(measureH c) =
      K * ∫ p, sliceSq c L1 G0 p.1 * (1 + p.2.2 ^ 2)⁻¹ ∂(measureH c) :=
    MeasureTheory.integral_const_mul _ _
  have hg1_eq : ∫ p, g1 p ∂(measureH c) =
      K * ∫ p, sliceSq c L1 G1 p.1 * (1 + p.2.2 ^ 2)⁻¹ ∂(measureH c) :=
    MeasureTheory.integral_const_mul _ _
  rw [hgF_eq, hg0_eq, hg1_eq] at hmono
  have hF_cell := integral_cvec_measureH_le (c := c) hσ hσH1 hL1 hF.1 hF_supp
  obtain ⟨hcoeff1, hcoeff2⟩ := box_coeff_bounds hc hσ hσH1 hL1 h1Γ hc_Γ hA_Γ
  have hI_F_nn : 0 ≤ ∫ p, ‖cvec (F p)‖ ^ 2 ∂(cellMeasure c) :=
    integral_nonneg fun _ => sq_nonneg _
  have hI_G0_nn : 0 ≤ ∫ p, ‖cvec (G0 p)‖ ^ 2 ∂(cellMeasure c) :=
    integral_nonneg fun _ => sq_nonneg _
  have hI_G1_nn : 0 ≤ ∫ p, ‖cvec (G1 p)‖ ^ 2 ∂(cellMeasure c) :=
    integral_nonneg fun _ => sq_nonneg _
  have htermF : (1 + L1) ^ 4 * ∫ p, ‖cvec (lerayField c F p)‖ ^ 2 ∂(measureH c) ≤
      (16 * Γ ^ 10) ^ 2 * ∫ p, ‖cvec (F p)‖ ^ 2 ∂(cellMeasure c) := by
    calc (1 + L1) ^ 4 * ∫ p, ‖cvec (lerayField c F p)‖ ^ 2 ∂(measureH c)
        ≤ (1 + L1) ^ 4 * ((1 + σ⁻¹ + H1 + L1) ^ 2 * ∫ p, ‖cvec (F p)‖ ^ 2 ∂(cellMeasure c)) :=
          mul_le_mul_of_nonneg_left (hleF.trans hF_cell) (by positivity)
      _ = ((1 + L1) ^ 4 * (1 + σ⁻¹ + H1 + L1) ^ 2) * ∫ p, ‖cvec (F p)‖ ^ 2 ∂(cellMeasure c) := by ring
      _ ≤ (16 * Γ ^ 10) ^ 2 * ∫ p, ‖cvec (F p)‖ ^ 2 ∂(cellMeasure c) :=
          mul_le_mul_of_nonneg_right hcoeff1 hI_F_nn
  have htermG0 : K * ∫ p, sliceSq c L1 G0 p.1 * (1 + p.2.2 ^ 2)⁻¹ ∂(measureH c) ≤
      (16 * Γ ^ 10) ^ 2 * ∫ p, ‖cvec (G0 p)‖ ^ 2 ∂(cellMeasure c) := by
    calc K * ∫ p, sliceSq c L1 G0 p.1 * (1 + p.2.2 ^ 2)⁻¹ ∂(measureH c)
        ≤ K * (4 * c * (1 + σ⁻¹ + H1 + L1) ^ 2 * ∫ p, ‖cvec (G0 p)‖ ^ 2 ∂(cellMeasure c)) :=
          mul_le_mul_of_nonneg_left hleG0 hK0
      _ = (K * (4 * c * (1 + σ⁻¹ + H1 + L1) ^ 2)) * ∫ p, ‖cvec (G0 p)‖ ^ 2 ∂(cellMeasure c) := by ring
      _ ≤ (16 * Γ ^ 10) ^ 2 * ∫ p, ‖cvec (G0 p)‖ ^ 2 ∂(cellMeasure c) :=
          mul_le_mul_of_nonneg_right hcoeff2 hI_G0_nn
  have htermG1 : K * ∫ p, sliceSq c L1 G1 p.1 * (1 + p.2.2 ^ 2)⁻¹ ∂(measureH c) ≤
      (16 * Γ ^ 10) ^ 2 * ∫ p, ‖cvec (G1 p)‖ ^ 2 ∂(cellMeasure c) := by
    calc K * ∫ p, sliceSq c L1 G1 p.1 * (1 + p.2.2 ^ 2)⁻¹ ∂(measureH c)
        ≤ K * (4 * c * (1 + σ⁻¹ + H1 + L1) ^ 2 * ∫ p, ‖cvec (G1 p)‖ ^ 2 ∂(cellMeasure c)) :=
          mul_le_mul_of_nonneg_left hleG1 hK0
      _ = (K * (4 * c * (1 + σ⁻¹ + H1 + L1) ^ 2)) * ∫ p, ‖cvec (G1 p)‖ ^ 2 ∂(cellMeasure c) := by ring
      _ ≤ (16 * Γ ^ 10) ^ 2 * ∫ p, ‖cvec (G1 p)‖ ^ 2 ∂(cellMeasure c) :=
          mul_le_mul_of_nonneg_right hcoeff2 hI_G1_nn
  linarith

/-! ### 5. Source Field Derivative Bounds and `H^6` Control -/

open IterDecayAux in
lemma contDiff_iterDF :
    ∀ (k : ℕ) (g : Fin k → Chart) {W : Chart → Fin 2 → ℝ},
      (∀ l, ContDiff ℝ ∞ (fun p => W p l)) →
      ∀ l, ContDiff ℝ ∞ (fun p => iterDF k g W p l)
  | 0, _, _, hWs, l => hWs l
  | k + 1, g, _, hWs, l =>
      ((contDiff_iterDF k (fun j => g j.succ) hWs l).fderiv_right (by simp)).clm_apply
        contDiff_const

open IterDecayAux in
lemma dfDv_iterDF :
    ∀ (k : ℕ) (g : Fin k → Chart) {W : Chart → Fin 2 → ℝ},
      (∀ l, ContDiff ℝ ∞ (fun p => W p l)) → ∀ (u : Chart),
      dfDv (iterDF k g W) u = iterDF k g (dfDv W u)
  | 0, _, _, _, _ => rfl
  | k + 1, g, _, hWs, u => by
      simp only [iterDF]
      rw [dfDv_comm (contDiff_iterDF k (fun j => g j.succ) hWs),
        dfDv_iterDF k (fun j => g j.succ) hWs u]

open IterDecayAux in
lemma iterDF_add :
    ∀ (k : ℕ) (g : Fin k → Chart) {W1 W2 : Chart → Fin 2 → ℝ},
      (∀ l, ContDiff ℝ ∞ (fun p => W1 p l)) →
      (∀ l, ContDiff ℝ ∞ (fun p => W2 p l)) →
      iterDF k g (fun p l => W1 p l + W2 p l) =
        fun p l => iterDF k g W1 p l + iterDF k g W2 p l
  | 0, _, _, _, _, _ => rfl
  | k + 1, g, W1, W2, hW1, hW2 => by
      ext p l
      simp only [iterDF, iterDF_add k (fun j => g j.succ) hW1 hW2]
      have h1 := (((contDiff_iterDF k (fun j => g j.succ) hW1 l).differentiable (by simp)) p).hasFDerivAt
      have h2 := (((contDiff_iterDF k (fun j => g j.succ) hW2 l).differentiable (by simp)) p).hasFDerivAt
      change fderiv ℝ ((fun q => iterDF k (fun j => g j.succ) W1 q l) +
          (fun q => iterDF k (fun j => g j.succ) W2 q l)) p (g 0) = _
      rw [(h1.add h2).fderiv]
      rfl

open IterDecayAux in
lemma iterDF_const_mul :
    ∀ (k : ℕ) (g : Fin k → Chart) (c0 : ℝ) {W : Chart → Fin 2 → ℝ},
      (∀ l, ContDiff ℝ ∞ (fun p => W p l)) →
      iterDF k g (fun p l => c0 * W p l) =
        fun p l => c0 * iterDF k g W p l
  | 0, _, _, _, _ => rfl
  | k + 1, g, c0, W, hW => by
      ext p l
      simp only [iterDF, iterDF_const_mul k (fun j => g j.succ) c0 hW]
      have h1 := ((contDiff_iterDF k (fun j => g j.succ) hW l).differentiable (by simp)) p
      change fderiv ℝ (fun q => c0 * iterDF k (fun j => g j.succ) W q l) p (g 0) = _
      rw [fderiv_const_mul h1]
      rfl

open IterDecayAux in
lemma dfDv_sMul {W : Chart → Fin 2 → ℝ} (hWs : ∀ l, ContDiff ℝ ∞ (fun p => W p l))
    (u : Chart) :
    dfDv (sMul W) u =
      fun p l => sMul (dfDv W u) p l + u.1 * W p l := by
  ext p l
  have hd1 : HasFDerivAt (fun q : Chart => q.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst
  have hd2 : HasFDerivAt (fun q : Chart => W q l) (fderiv ℝ (fun q => W q l) p) p :=
    (((hWs l).differentiable (by simp)) p).hasFDerivAt
  have hmul : fderiv ℝ (fun q : Chart => q.1 * W q l) p =
      p.1 • fderiv ℝ (fun q => W q l) p + W p l • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) :=
    (hd1.mul hd2).fderiv
  change fderiv ℝ (fun q : Chart => q.1 * W q l) p u =
    p.1 * fderiv ℝ (fun q => W q l) p u + u.1 * W p l
  rw [hmul]
  change p.1 * fderiv ℝ (fun q => W q l) p u + W p l * u.1 =
    p.1 * fderiv ℝ (fun q => W q l) p u + u.1 * W p l
  ring

open IterDecayAux in
lemma abs_iterDF_sMul_le :
    ∀ (k : ℕ) {W : Chart → Fin 2 → ℝ} (_hWs : ∀ l, ContDiff ℝ ∞ (fun q => W q l))
      {p : Chart} {M : ℝ}
      (_hW : ∀ (d : ℕ) (h : Fin d → Chart), d ≤ k → (∀ j, ‖h j‖ ≤ 1) →
        ∀ l, |iterDF d h W p l| ≤ M)
      (g : Fin k → Chart) (_hg : ∀ j, ‖g j‖ ≤ 1) (l : Fin 2),
      |iterDF k g (sMul W) p l| ≤ (|p.1| + k) * M
  | 0, W, _, p, M, hW, g, hg, l => by
      have h0 := hW 0 g le_rfl hg l
      calc |iterDF 0 g (sMul W) p l|
          = |p.1| * |iterDF 0 g W p l| := abs_mul p.1 (W p l)
        _ ≤ |p.1| * M := mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
        _ = (|p.1| + (0 : ℕ)) * M := by simp
  | k + 1, W, hWs, p, M, hW, g, hg, l => by
      set g' : Fin k → Chart := fun j => g j.succ
      have hg' : ∀ j, ‖g' j‖ ≤ 1 := fun j => hg j.succ
      have hWs' : ∀ i, ContDiff ℝ ∞ (fun q => dfDv W (g 0) q i) :=
        fun i => ((hWs i).fderiv_right (by simp)).clm_apply contDiff_const
      have hstep : iterDF (k + 1) g (sMul W) p l =
          iterDF k g' (sMul (dfDv W (g 0))) p l +
            (g 0).1 * iterDF k g' W p l := by
        change dfDv (iterDF k g' (sMul W)) (g 0) p l = _
        rw [dfDv_iterDF k g' (W := sMul W) (fun i => contDiff_fst.mul (hWs i)) (g 0),
          dfDv_sMul hWs (g 0),
          iterDF_add k g' (W1 := sMul (dfDv W (g 0))) (W2 := fun q i => (g 0).1 * W q i)
            (fun i => contDiff_fst.mul (hWs' i)) (fun i => contDiff_const.mul (hWs i)),
          iterDF_const_mul k g' (g 0).1 hWs]
      have hW' : ∀ (d : ℕ) (h : Fin d → Chart), d ≤ k → (∀ j, ‖h j‖ ≤ 1) →
          ∀ i, |iterDF d h (dfDv W (g 0)) p i| ≤ M := by
        intro d h hd hh i
        rw [← dfDv_iterDF d h hWs (g 0)]
        exact hW (d + 1) (Fin.cons (g 0) h) (Nat.succ_le_succ hd)
          (fun j => Fin.cases (hg 0) hh j) i
      have h1 := abs_iterDF_sMul_le k hWs' hW' g' hg' l
      have h2 := hW k g' (Nat.le_succ k) hg' l
      have hg0 : |(g 0).1| ≤ 1 := (Real.norm_eq_abs _ ▸ norm_fst_le (g 0)).trans (hg 0)
      have h2' : |(g 0).1 * iterDF k g' W p l| ≤ M := by
        rw [abs_mul]
        calc |(g 0).1| * |iterDF k g' W p l|
            ≤ 1 * M := mul_le_mul hg0 h2 (abs_nonneg _) zero_le_one
          _ = M := one_mul M
      rw [hstep]
      calc |iterDF k g' (sMul (dfDv W (g 0))) p l + (g 0).1 * iterDF k g' W p l|
          ≤ |iterDF k g' (sMul (dfDv W (g 0))) p l| +
              |(g 0).1 * iterDF k g' W p l| := abs_add_le _ _
        _ ≤ (|p.1| + k) * M + M := add_le_add h1 h2'
        _ = (|p.1| + ↑(k + 1)) * M := by push_cast; ring

lemma norm_lfpDir (i : Fin 2) : ‖lfpDir i‖ ≤ 1 := by
  fin_cases i <;> simp [lfpDir, Prod.norm_def]

lemma norm_profDir (j : Fin 3) : ‖IterDecayAux.profDir j‖ ≤ 1 := by
  fin_cases j <;> simp [IterDecayAux.profDir, Prod.norm_def]

lemma norm_e1_le_one : ‖((1 : ℝ), (0 : ℝ), (0 : ℝ))‖ ≤ 1 := by
  simp [Prod.norm_def]

open IterDecayAux in
lemma iterDF_supp_of_supp {σ H1 L1 : ℝ} :
    ∀ (k : ℕ) (g : Fin k → Chart) {W : Chart → Fin 2 → ℝ},
      (∀ p : Chart, W p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
      ∀ p : Chart, iterDF k g W p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  | 0, _, _, hW_supp => hW_supp
  | k + 1, g, _, hW_supp =>
      dfDv_supp_of_supp (g 0) (iterDF_supp_of_supp k (fun j => g j.succ) hW_supp)

open IterDecayAux in
lemma opSF_iter_supp_of_supp {σ H1 L1 : ℝ} {W : Chart → Fin 2 → ℝ}
    (hW_supp : ∀ p : Chart, W p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    ∀ (a : ℕ) (p : Chart), (opSF^[a] W) p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  | 0, p, hp => hW_supp p hp
  | a + 1, p, hp => by
      rw [Function.iterate_succ'] at hp
      apply dfDv_supp_of_supp (1, 0, 0) (opSF_iter_supp_of_supp hW_supp a) p
      intro h0
      apply hp
      ext l
      simp [opSF, sMul, h0]

open IterDecayAux in
lemma abs_projReCLM_le (l : Fin 2) (w : MeridC) : |projReCLM l w| ≤ ‖w‖ := by
  have h1 : |(w l).re| ≤ ‖w l‖ := Complex.abs_re_le_norm (w l)
  have h2 : ‖w l‖ ≤ ‖w‖ := PiLp.norm_apply_le w l
  exact h1.trans h2

open IterDecayAux in
lemma abs_projImCLM_le (l : Fin 2) (w : MeridC) : |projImCLM l w| ≤ ‖w‖ := by
  have h1 : |(w l).im| ≤ ‖w l‖ := Complex.abs_im_le_norm (w l)
  have h2 : ‖w l‖ ≤ ‖w‖ := PiLp.norm_apply_le w l
  exact h1.trans h2

open IterDecayAux in
lemma abs_iterDF_base_le {z : Profile → MeridC} (hz : ContDiff ℝ ∞ z)
    {W : Chart → Fin 2 → ℝ} (hWs : ∀ l, ContDiff ℝ ∞ (fun p => W p l))
    (L : Fin 2 → MeridC →L[ℝ] ℝ) (hL : ∀ l w, |L l w| ≤ ‖w‖)
    (hLW : ∀ l p, L l (z p) = W p l)
    (d : ℕ) (h : Fin d → Chart) (hh : ∀ j, ‖h j‖ ≤ 1) (p : Chart) (l : Fin 2) :
    |iterDF d h W p l| ≤ ‖iteratedFDeriv ℝ d z p‖ := by
  have heq := clm_iteratedFDeriv_opS_eq_iterDF (L l) hz hWs l (hLW l) 0 d h p
  simp only [Function.iterate_zero, id_eq] at heq
  rw [← heq]
  have hprod : ∏ j : Fin d, ‖h j‖ ≤ 1 :=
    Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => hh j)
  calc |L l (iteratedFDeriv ℝ d z p h)|
      ≤ ‖iteratedFDeriv ℝ d z p h‖ := hL l _
    _ ≤ ‖iteratedFDeriv ℝ d z p‖ * ∏ j : Fin d, ‖h j‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ ‖iteratedFDeriv ℝ d z p‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ d z p‖ := mul_one _

open IterDecayAux in
lemma cvec_iterDF_opSF_sq_le {σ H1 L1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {z : Profile → MeridC} {W : Chart → Fin 2 → ℝ}
    (hWs : ∀ l, ContDiff ℝ ∞ (fun p => W p l))
    (hW_supp : ∀ p : Chart, W p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hW_bd : ∀ (d : ℕ) (h : Fin d → Chart), (∀ j, ‖h j‖ ≤ 1) →
      ∀ (p : Chart) (l : Fin 2), |iterDF d h W p l| ≤ ‖iteratedFDeriv ℝ d z p‖)
    {a k : ℕ} (ha : a < 2) (hk : k ≤ 5) (g : Fin k → Chart) (hg : ∀ j, ‖g j‖ ≤ 1)
    (p : Chart) :
    ‖cvec (iterDF k g (opSF^[a] W) p)‖ ^ 2 ≤
      (24 * (1 + H1)) ^ 2 * ∑ d ∈ Finset.range 7, ‖iteratedFDeriv ℝ d z p‖ ^ 2 := by
  have hH1 : 0 ≤ H1 := hσ.le.trans hσH1
  by_cases hp : p ∈ dtdBand σ H1 L1
  · obtain ⟨hp1, hp2, _⟩ := hp
    set M : ℝ := ∑ d ∈ Finset.range 7, ‖iteratedFDeriv ℝ d z p‖
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hW_M : ∀ (d : ℕ) (h : Fin d → Chart), d ≤ 6 → (∀ j, ‖h j‖ ≤ 1) →
        ∀ l, |iterDF d h W p l| ≤ M := by
      intro d h hd hh l
      have hd7 : d ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
      exact (hW_bd d h hh p l).trans
        (Finset.single_le_sum (fun m _ => norm_nonneg (iteratedFDeriv ℝ m z p)) hd7)
    have hcomp : ∀ l : Fin 2, |iterDF k g (opSF^[a] W) p l| ≤ 6 * (1 + H1) * M := by
      intro l
      interval_cases a
      · simp only [Function.iterate_zero, id_eq]
        have h1 := hW_M k g (by omega) hg l
        calc |iterDF k g W p l|
            ≤ M := h1
          _ ≤ 6 * (1 + H1) * M :=
              le_mul_of_one_le_left hM0 (by linarith)
      · simp only [Function.iterate_one, opSF]
        have hW1 : ∀ (d : ℕ) (h : Fin d → Chart), d ≤ k → (∀ j, ‖h j‖ ≤ 1) →
            ∀ i, |iterDF d h (dfDv W (1, 0, 0)) p i| ≤ M := by
          intro d h hd hh i
          rw [← dfDv_iterDF d h hWs (1, 0, 0)]
          exact hW_M (d + 1) (Fin.cons (1, 0, 0) h) (by omega)
            (fun j => Fin.cases norm_e1_le_one hh j) i
        have h1 := abs_iterDF_sMul_le k
          (fun i => ((hWs i).fderiv_right (by simp)).clm_apply contDiff_const)
          hW1 g hg l
        have hp_abs : |p.1| = p.1 := abs_of_pos (hσ.trans_le hp1)
        have hk_le : (k : ℝ) ≤ 5 := by exact_mod_cast hk
        have hfactor : |p.1| + (k : ℝ) ≤ 6 * (1 + H1) := by linarith
        exact h1.trans (mul_le_mul_of_nonneg_right hfactor hM0)
    have h0 := hcomp 0
    have h1 := hcomp 1
    have hsq0 : (iterDF k g (opSF^[a] W) p 0) ^ 2 ≤ (6 * (1 + H1) * M) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h0 2
    have hsq1 : (iterDF k g (opSF^[a] W) p 1) ^ 2 ≤ (6 * (1 + H1) * M) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hcs : M ^ 2 ≤ 7 * ∑ d ∈ Finset.range 7, ‖iteratedFDeriv ℝ d z p‖ ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range 7)
        (fun _ => (1 : ℝ)) (fun d => ‖iteratedFDeriv ℝ d z p‖)
      simpa [M] using h
    rw [norm_cvec_sq]
    calc (iterDF k g (opSF^[a] W) p 0) ^ 2 + (iterDF k g (opSF^[a] W) p 1) ^ 2
        ≤ (6 * (1 + H1) * M) ^ 2 + (6 * (1 + H1) * M) ^ 2 := add_le_add hsq0 hsq1
      _ = 72 * (1 + H1) ^ 2 * M ^ 2 := by ring
      _ ≤ 72 * (1 + H1) ^ 2 * (7 * ∑ d ∈ Finset.range 7, ‖iteratedFDeriv ℝ d z p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = 504 * (1 + H1) ^ 2 * ∑ d ∈ Finset.range 7, ‖iteratedFDeriv ℝ d z p‖ ^ 2 := by ring
      _ ≤ 576 * (1 + H1) ^ 2 * ∑ d ∈ Finset.range 7, ‖iteratedFDeriv ℝ d z p‖ ^ 2 := by
          gcongr
          norm_num
      _ = (24 * (1 + H1)) ^ 2 * ∑ d ∈ Finset.range 7, ‖iteratedFDeriv ℝ d z p‖ ^ 2 := by ring
  · have hzero : iterDF k g (opSF^[a] W) p = 0 := by
      by_contra hne
      exact hp (iterDF_supp_of_supp k g (opSF_iter_supp_of_supp hW_supp a) p hne)
    rw [norm_cvec_sq, hzero]
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

open IterDecayAux in
lemma integral_cvec_iterDF_opSF_sq_le {c σ H1 L1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {z : Profile → MeridC} (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    {W : Chart → Fin 2 → ℝ} (hWs : ∀ l, ContDiff ℝ ∞ (fun p => W p l))
    (hW_supp : ∀ p : Chart, W p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hW_bd : ∀ (d : ℕ) (h : Fin d → Chart), (∀ j, ‖h j‖ ≤ 1) →
      ∀ (p : Chart) (l : Fin 2), |iterDF d h W p l| ≤ ‖iteratedFDeriv ℝ d z p‖)
    {a k : ℕ} (ha : a < 2) (hk : k ≤ 5) (g : Fin k → Chart) (hg : ∀ j, ‖g j‖ ≤ 1) :
    ∫ p, ‖cvec (iterDF k g (opSF^[a] W) p)‖ ^ 2 ∂(cellMeasure c) ≤
      (64 * (1 + H1) * h6Norm c z) ^ 2 := by
  have hH1 : 0 ≤ H1 := hσ.le.trans hσH1
  have hint_d : ∀ d : ℕ,
      Integrable (fun p : Profile => ‖iteratedFDeriv ℝ d z p‖ ^ 2) (cellMeasure c) :=
    fun d => ObsBoxS1Aux.integrableOn_iteratedFDeriv_sq c σ H1 L1 hz hsupp d
  have hint_sum : Integrable
      (fun p : Profile => ∑ d ∈ Finset.range 7, ‖iteratedFDeriv ℝ d z p‖ ^ 2)
      (cellMeasure c) :=
    integrable_finsetSum (Finset.range 7) fun d _ => hint_d d
  have hmono := integral_mono_of_nonneg
    (ae_of_all _ fun _ => sq_nonneg _)
    (hint_sum.const_mul ((24 * (1 + H1)) ^ 2))
    (ae_of_all _ (cvec_iterDF_opSF_sq_le hσ hσH1 hWs hW_supp hW_bd ha hk g hg))
  rw [MeasureTheory.integral_const_mul,
    integral_finsetSum (Finset.range 7) fun d _ => hint_d d] at hmono
  have hd_le : ∀ d ∈ Finset.range 7,
      ∫ p, ‖iteratedFDeriv ℝ d z p‖ ^ 2 ∂(cellMeasure c) ≤ (h6Norm c z) ^ 2 := by
    intro d hd
    set Id : ℝ := ∫ p, ‖iteratedFDeriv ℝ d z p‖ ^ 2 ∂(cellMeasure c)
    have hId0 : 0 ≤ Id := integral_nonneg fun _ => sq_nonneg _
    have hsingle : Id ^ (1 / 2 : ℝ) ≤ h6Norm c z := by
      unfold h6Norm
      exact Finset.single_le_sum
        (f := fun m => (∫ p, ‖iteratedFDeriv ℝ m z p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ))
        (fun m _ => Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _) hd
    have hsq := pow_le_pow_left₀ (Real.rpow_nonneg hId0 _) hsingle 2
    have hId_eq : (Id ^ (1 / 2 : ℝ)) ^ 2 = Id := by
      rw [← Real.rpow_natCast (Id ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hId0]
      norm_num
    rwa [hId_eq] at hsq
  have hsum_le : ∑ d ∈ Finset.range 7, ∫ p, ‖iteratedFDeriv ℝ d z p‖ ^ 2 ∂(cellMeasure c) ≤
      7 * (h6Norm c z) ^ 2 := by
    calc ∑ d ∈ Finset.range 7, ∫ p, ‖iteratedFDeriv ℝ d z p‖ ^ 2 ∂(cellMeasure c)
        ≤ ∑ _d ∈ Finset.range 7, (h6Norm c z) ^ 2 := Finset.sum_le_sum hd_le
      _ = 7 * (h6Norm c z) ^ 2 := by simp [Finset.sum_const]
  calc ∫ p, ‖cvec (iterDF k g (opSF^[a] W) p)‖ ^ 2 ∂(cellMeasure c)
      ≤ (24 * (1 + H1)) ^ 2 *
          ∑ d ∈ Finset.range 7, ∫ p, ‖iteratedFDeriv ℝ d z p‖ ^ 2 ∂(cellMeasure c) := hmono
    _ ≤ (24 * (1 + H1)) ^ 2 * (7 * (h6Norm c z) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_le (sq_nonneg _)
    _ = 4032 * (1 + H1) ^ 2 * (h6Norm c z) ^ 2 := by ring
    _ ≤ 4096 * (1 + H1) ^ 2 * (h6Norm c z) ^ 2 := by
        gcongr
        norm_num
    _ = (64 * (1 + H1) * h6Norm c z) ^ 2 := by ring

open IterDecayAux in
lemma single_source_weighted_le {c σ H1 L1 Γ : ℝ}
    (hc : 0 < c) (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    (h1Γ : 1 ≤ Γ) (hc_Γ : 1 + c + c⁻¹ ≤ Γ) (hA_Γ : 1 + σ⁻¹ + H1 + L1 ≤ Γ)
    {z : Profile → MeridC} (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    {W : Chart → Fin 2 → ℝ} (hW : IsForceField c W)
    (hW_supp : ∀ p : Chart, W p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hW_bd : ∀ (d : ℕ) (h : Fin d → Chart), (∀ j, ‖h j‖ ≤ 1) →
      ∀ (p : Chart) (l : Fin 2), |iterDF d h W p l| ≤ ‖iteratedFDeriv ℝ d z p‖)
    {a j m : ℕ} (ha : a < 2) (hj : j < 3) (hm : m < 5)
    (g : Fin m → Chart) (hg : ∀ k, ‖g k‖ ≤ 1) :
    Integrable
      (fun p : Chart => (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c (iterDF m g (opSF^[a] W)) p)‖ ^ 2)
      (measureH c) ∧
    ∫ p, (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c (iterDF m g (opSF^[a] W)) p)‖ ^ 2 ∂(measureH c) ≤
      (2048 * Γ ^ 11 * h6Norm c z) ^ 2 := by
  set F : Chart → Fin 2 → ℝ := iterDF m g (opSF^[a] W)
  have hF : IsForceField c F := isForceField_iterDF m g (isForceField_opSF_iter hW a)
  have hF_supp := iterDF_supp_of_supp m g (opSF_iter_supp_of_supp hW_supp a)
  obtain ⟨hi_lhs, hle_lhs⟩ :=
    integral_weighted_lerayField_sq_le hc hσ hσH1 hL1 h1Γ hc_Γ hA_Γ hF hF_supp hj
  refine ⟨hi_lhs, ?_⟩
  have h0_le : ∫ p, ‖cvec (F p)‖ ^ 2 ∂(cellMeasure c) ≤ (64 * (1 + H1) * h6Norm c z) ^ 2 :=
    integral_cvec_iterDF_opSF_sq_le hσ hσH1 hz hsupp hW.1 hW_supp hW_bd ha (by omega) g hg
  have hG0_le : ∫ p, ‖cvec (dfDv F (lfpDir 0) p)‖ ^ 2 ∂(cellMeasure c) ≤
      (64 * (1 + H1) * h6Norm c z) ^ 2 :=
    integral_cvec_iterDF_opSF_sq_le hσ hσH1 hz hsupp hW.1 hW_supp hW_bd ha (by omega)
      (Fin.cons (lfpDir 0) g) (fun k => Fin.cases (norm_lfpDir 0) hg k)
  have hG1_le : ∫ p, ‖cvec (dfDv F (lfpDir 1) p)‖ ^ 2 ∂(cellMeasure c) ≤
      (64 * (1 + H1) * h6Norm c z) ^ 2 :=
    integral_cvec_iterDF_opSF_sq_le hσ hσH1 hz hsupp hW.1 hW_supp hW_bd ha (by omega)
      (Fin.cons (lfpDir 1) g) (fun k => Fin.cases (norm_lfpDir 1) hg k)
  have hH1 : 0 ≤ H1 := hσ.le.trans hσH1
  have hσ_inv : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have h1H1_Γ : 1 + H1 ≤ Γ := by linarith
  have hh6_nn : 0 ≤ h6Norm c z :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _
  have hbase_le : 64 * (1 + H1) * h6Norm c z ≤ 64 * Γ * h6Norm c z := by
    gcongr
  have hsq_le : (64 * (1 + H1) * h6Norm c z) ^ 2 ≤ (64 * Γ * h6Norm c z) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hbase_le 2
  have hsum3 : ∫ p, ‖cvec (F p)‖ ^ 2 ∂(cellMeasure c) +
      ∫ p, ‖cvec (dfDv F (lfpDir 0) p)‖ ^ 2 ∂(cellMeasure c) +
      ∫ p, ‖cvec (dfDv F (lfpDir 1) p)‖ ^ 2 ∂(cellMeasure c) ≤
      3 * (64 * Γ * h6Norm c z) ^ 2 := by
    linarith
  calc ∫ p, (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c F p)‖ ^ 2 ∂(measureH c)
      ≤ (16 * Γ ^ 10) ^ 2 * (3 * (64 * Γ * h6Norm c z) ^ 2) :=
        hle_lhs.trans (mul_le_mul_of_nonneg_left hsum3 (sq_nonneg _))
    _ = 3145728 * Γ ^ 22 * (h6Norm c z) ^ 2 := by ring
    _ ≤ 4194304 * Γ ^ 22 * (h6Norm c z) ^ 2 := by
        gcongr
        norm_num
    _ = (2048 * Γ ^ 11 * h6Norm c z) ^ 2 := by ring

open IterDecayAux in
lemma sum_abs_le_two_norm_cvec (v : Fin 2 → ℝ) :
    ∑ i : Fin 2, |v i| ≤ 2 * ‖cvec v‖ := by
  rw [Fin.sum_univ_two]
  have hsq : (|v 0| + |v 1|) ^ 2 ≤ (2 * ‖cvec v‖) ^ 2 := by
    rw [mul_pow, norm_cvec_sq]
    nlinarith [sq_nonneg (|v 0| - |v 1|), sq_abs (v 0), sq_abs (v 1)]
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

open IterDecayAux in
lemma single_moment_term_le {c σ H1 L1 Γ : ℝ}
    (hc : 0 < c) (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    (h1Γ : 1 ≤ Γ) (hc_Γ : 1 + c + c⁻¹ ≤ Γ) (hA_Γ : 1 + σ⁻¹ + H1 + L1 ≤ Γ)
    {z : Profile → MeridC} (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    {a j m : ℕ} (ha : a ∈ Finset.range 2) (hj : j ∈ Finset.range 3) (hm : m ∈ Finset.range 5) :
    (∫ p, (|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖ ^ 2
      ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
      663552 * Γ ^ 11 * h6Norm c z := by
  have ha' : a < 2 := Finset.mem_range.mp ha
  have hj' : j < 3 := Finset.mem_range.mp hj
  have hm' : m < 5 := Finset.mem_range.mp hm
  have hΓ0 : 0 ≤ Γ := zero_le_one.trans h1Γ
  have hh6_nn : 0 ≤ h6Norm c z :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _
  have hsm : ContDiff ℝ ∞ (flatLerayRep c z) := flatLerayRep_smooth hc hσ hz hsupp
  have hReF : IsForceField c (meridReField z) := isForceField_meridReField hσ hz hsupp
  have hImF : IsForceField c (meridImField z) := isForceField_meridImField hσ hz hsupp
  have hRe_supp : ∀ p : Chart, meridReField z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
    intro p hp
    apply hsupp p
    intro hz0
    apply hp
    ext l
    simp [meridReField, hz0]
  have hIm_supp : ∀ p : Chart, meridImField z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
    intro p hp
    apply hsupp p
    intro hz0
    apply hp
    ext l
    simp [meridImField, hz0]
  have hRe_bd := abs_iterDF_base_le hz.smooth hReF.1 projReCLM abs_projReCLM_le
    (fun _ _ => rfl)
  have hIm_bd := abs_iterDF_base_le hz.smooth hImF.1 projImCLM abs_projImCLM_le
    (fun _ _ => rfl)
  set gr : (Fin m → Fin 3) → (Fin m → Chart) := fun r k => profDir (r k)
  have hgr : ∀ (r : Fin m → Fin 3) (k : Fin m), ‖gr r k‖ ≤ 1 :=
    fun r k => norm_profDir (r k)
  set fRe : (Fin m → Fin 3) → Chart → ℝ := fun r p =>
    (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridReField z))) p)‖ ^ 2
  set fIm : (Fin m → Fin 3) → Chart → ℝ := fun r p =>
    (|p.2.2| ^ j) ^ 2 * ‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridImField z))) p)‖ ^ 2
  have hRe_int_le : ∀ r : Fin m → Fin 3,
      Integrable (fRe r) (measureH c) ∧
      ∫ p, fRe r p ∂(measureH c) ≤ (2048 * Γ ^ 11 * h6Norm c z) ^ 2 :=
    fun r => single_source_weighted_le hc hσ hσH1 hL1 h1Γ hc_Γ hA_Γ hz hsupp
      hReF hRe_supp hRe_bd ha' hj' hm' (gr r) (hgr r)
  have hIm_int_le : ∀ r : Fin m → Fin 3,
      Integrable (fIm r) (measureH c) ∧
      ∫ p, fIm r p ∂(measureH c) ≤ (2048 * Γ ^ 11 * h6Norm c z) ^ 2 :=
    fun r => single_source_weighted_le hc hσ hσH1 hL1 h1Γ hc_Γ hA_Γ hz hsupp
      hImF hIm_supp hIm_bd ha' hj' hm' (gr r) (hgr r)
  have hpt : ∀ p : Profile,
      (|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖ ^ 2 ≤
        648 * ∑ r : Fin m → Fin 3, (fRe r p + fIm r p) := by
    intro p
    have h1 := norm_multilinear_profile_le m (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p)
    have h2 : ∀ r : Fin m → Fin 3,
        ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p (gr r)‖ ≤
          2 * ‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridReField z))) p)‖ +
            2 * ‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridImField z))) p)‖ := by
      intro r
      have hproj := norm_meridC_le_sum_proj
        (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p (gr r))
      have hRe_eq : ∀ i : Fin 2,
          projReCLM i (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p (gr r)) =
            lerayField c (iterDF m (gr r) (opSF^[a] (meridReField z))) p i := by
        intro i
        rw [clm_iteratedFDeriv_opS_eq_iterDF (projReCLM i) hsm
          (lerayFieldProps c hc (meridReField z) hReF).1 i
          (fun q => projReCLM_flatLerayRep c z q i) a m (gr r) p,
          opSF_iter_lerayField hc hReF a,
          iterDF_lerayField hc m (gr r) (isForceField_opSF_iter hReF a)]
      have hIm_eq : ∀ i : Fin 2,
          projImCLM i (iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p (gr r)) =
            lerayField c (iterDF m (gr r) (opSF^[a] (meridImField z))) p i := by
        intro i
        rw [clm_iteratedFDeriv_opS_eq_iterDF (projImCLM i) hsm
          (lerayFieldProps c hc (meridImField z) hImF).1 i
          (fun q => projImCLM_flatLerayRep c z q i) a m (gr r) p,
          opSF_iter_lerayField hc hImF a,
          iterDF_lerayField hc m (gr r) (isForceField_opSF_iter hImF a)]
      simp_rw [hRe_eq, hIm_eq, Finset.sum_add_distrib] at hproj
      exact hproj.trans (add_le_add (sum_abs_le_two_norm_cvec _) (sum_abs_le_two_norm_cvec _))
    have h3 : ∀ r : Fin m → Fin 3,
        ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p (gr r)‖ ^ 2 ≤
          8 * (‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridReField z))) p)‖ ^ 2 +
            ‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridImField z))) p)‖ ^ 2) := by
      intro r
      have hr := pow_le_pow_left₀ (norm_nonneg _) (h2 r) 2
      nlinarith [sq_nonneg
        (‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridReField z))) p)‖ -
          ‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridImField z))) p)‖)]
    have hcard : (Finset.univ : Finset (Fin m → Fin 3)).card ≤ 81 := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      exact (Nat.pow_le_pow_right (by omega : 0 < 3) (by omega : m ≤ 4)).trans (by norm_num)
    have hcard_r : ((Finset.univ : Finset (Fin m → Fin 3)).card : ℝ) ≤ 81 := by
      exact_mod_cast hcard
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m → Fin 3))
      (fun _ => (1 : ℝ))
      (fun r => ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p (gr r)‖)
    simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at hcs
    have hsq_sum : ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖ ^ 2 ≤
        81 * ∑ r : Fin m → Fin 3,
          8 * (‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridReField z))) p)‖ ^ 2 +
            ‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridImField z))) p)‖ ^ 2) := by
      calc ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖ ^ 2
          ≤ (∑ r : Fin m → Fin 3,
              ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p (gr r)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ ((Finset.univ : Finset (Fin m → Fin 3)).card : ℝ) *
              ∑ r : Fin m → Fin 3,
                ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p (gr r)‖ ^ 2 := hcs
        _ ≤ 81 * ∑ r : Fin m → Fin 3,
              ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p (gr r)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hcard_r (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        _ ≤ 81 * ∑ r : Fin m → Fin 3,
              8 * (‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridReField z))) p)‖ ^ 2 +
                ‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridImField z))) p)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => h3 r) (by norm_num)
    calc (|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖ ^ 2
        ≤ (|p.2.2| ^ j) ^ 2 *
            (81 * ∑ r : Fin m → Fin 3,
              8 * (‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridReField z))) p)‖ ^ 2 +
                ‖cvec (lerayField c (iterDF m (gr r) (opSF^[a] (meridImField z))) p)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq_sum (sq_nonneg _)
      _ = 648 * ∑ r : Fin m → Fin 3, (fRe r p + fIm r p) := by
          dsimp only [fRe, fIm]
          simp_rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
  set fSum : (Fin m → Fin 3) → Chart → ℝ := fun r p => fRe r p + fIm r p
  have hfSum : ∀ r : Fin m → Fin 3, Integrable (fSum r) (measureH c) :=
    fun r => (hRe_int_le r).1.add (hIm_int_le r).1
  have hint_sum : Integrable
      (fun p : Profile => ∑ r : Fin m → Fin 3, fSum r p) (measureH c) :=
    integrable_finsetSum Finset.univ fun r _ => hfSum r
  have hmono := integral_mono_of_nonneg
    (ae_of_all _ fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (hint_sum.const_mul 648)
    (ae_of_all _ hpt)
  rw [MeasureTheory.integral_const_mul,
    integral_finsetSum Finset.univ fun r _ => hfSum r] at hmono
  have hr_le : ∀ r ∈ (Finset.univ : Finset (Fin m → Fin 3)),
      ∫ p, fSum r p ∂(measureH c) ≤
        2 * (2048 * Γ ^ 11 * h6Norm c z) ^ 2 := by
    intro r _
    change ∫ p, (fRe r p + fIm r p) ∂(measureH c) ≤ _
    rw [integral_add (hRe_int_le r).1 (hIm_int_le r).1]
    have h1 := (hRe_int_le r).2
    have h2 := (hIm_int_le r).2
    linarith
  have hcard : (Finset.univ : Finset (Fin m → Fin 3)).card ≤ 81 := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    exact (Nat.pow_le_pow_right (by omega : 0 < 3) (by omega : m ≤ 4)).trans (by norm_num)
  have hcard_r : ((Finset.univ : Finset (Fin m → Fin 3)).card : ℝ) ≤ 81 := by
    exact_mod_cast hcard
  have hsum_le : ∑ r : Fin m → Fin 3, ∫ p, fSum r p ∂(measureH c) ≤
      81 * (2 * (2048 * Γ ^ 11 * h6Norm c z) ^ 2) := by
    calc ∑ r : Fin m → Fin 3, ∫ p, fSum r p ∂(measureH c)
        ≤ ∑ _r : Fin m → Fin 3, 2 * (2048 * Γ ^ 11 * h6Norm c z) ^ 2 :=
          Finset.sum_le_sum hr_le
      _ = ((Finset.univ : Finset (Fin m → Fin 3)).card : ℝ) *
            (2 * (2048 * Γ ^ 11 * h6Norm c z) ^ 2) := by
          simp [Finset.sum_const]
      _ ≤ 81 * (2 * (2048 * Γ ^ 11 * h6Norm c z) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard_r (by positivity)
  have hint_tot : ∫ p, (|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖ ^ 2
      ∂(measureH c) ≤ (663552 * Γ ^ 11 * h6Norm c z) ^ 2 := by
    calc ∫ p, (|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖ ^ 2
          ∂(measureH c)
        ≤ 648 * ∑ r : Fin m → Fin 3, ∫ p, fSum r p ∂(measureH c) := hmono
      _ ≤ 648 * (81 * (2 * (2048 * Γ ^ 11 * h6Norm c z) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_le (by norm_num)
      _ = (663552 * Γ ^ 11 * h6Norm c z) ^ 2 := by ring
  set I : ℝ := ∫ p, (|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖ ^ 2
      ∂(measureH c)
  have hI0 : 0 ≤ I := integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hB0 : 0 ≤ 663552 * Γ ^ 11 * h6Norm c z := by positivity
  calc I ^ (1 / 2 : ℝ)
      ≤ ((663552 * Γ ^ 11 * h6Norm c z) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hI0 hint_tot (by norm_num)
    _ = 663552 * Γ ^ 11 * h6Norm c z := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hB0]
        norm_num

end MomentNormAux

open MomentNormAux in
/-- **Weighted moment-norm bound for `flatLerayRep c z` (`FlatLerayMomentNormBound`,
task `PartII-a:N04/2/1/2`).** -/
theorem flatLerayMomentNormBound : FlatLerayMomentNormBound := by
  refine ⟨11, 30 * 663552, by norm_num, ?_⟩
  intro ν c σ H1 L1 M γs hν hc hσ hσH1 hL1 hM hγs z hz hsupp
  set Γ : ℝ := GammaBox ν c σ H1 L1 M γs
  have h1Γ : 1 ≤ Γ := one_le_GammaBox hν hc hσ hσH1 hL1 hM hγs
  have hc_Γ : 1 + c + c⁻¹ ≤ Γ := one_add_c_add_inv_c_le_GammaBox ν c σ H1 L1 M γs hν hσ hσH1 hL1 hM hγs
  have hA_Γ : 1 + σ⁻¹ + H1 + L1 ≤ Γ := one_add_sigma_H1_L1_le_GammaBox ν c σ H1 L1 M γs hν hc hM hγs
  unfold flatProjMomentNorm
  calc ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 3, ∑ m ∈ Finset.range 5,
        (∫ p, (|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖ ^ 2
          ∂(measureH c)) ^ (1 / 2 : ℝ)
      ≤ ∑ _a ∈ Finset.range 2, ∑ _j ∈ Finset.range 3, ∑ _m ∈ Finset.range 5,
          (663552 * Γ ^ 11 * h6Norm c z) := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun j hj =>
          Finset.sum_le_sum fun m hm => ?_
        exact single_moment_term_le hc hσ hσH1 hL1 h1Γ hc_Γ hA_Γ hz hsupp ha hj hm
    _ = 30 * 663552 * Γ ^ 11 * h6Norm c z := by
        simp [Finset.sum_const]
        ring

end UnforcedLeray.Short.PartIIa

