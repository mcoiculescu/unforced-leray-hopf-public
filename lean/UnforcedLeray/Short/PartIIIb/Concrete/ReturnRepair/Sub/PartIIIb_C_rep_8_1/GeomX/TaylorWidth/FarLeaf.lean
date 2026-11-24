import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Leaf
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.Diff

/-!
# `SepMeanFar` (helper for `PartIII-b:C/rep/8/1/1/1/3`)

Source `the November 2 reference manuscript` lines 5415-5427, 5439-5443,
3735-3766.  The proof of `IIIa.sepMeanPart` is rerun with the radial gap `D = ρ_i - ρ_o` replaced
by the sharper gap `D' = (ρ_i - ρ_o)|x_obs'|/ρ_i` (valid since `|x_obs'| ≥ ρ_i`): the integrands
are compared by `IIIa.mp_diff_pointwise` applied with `ρ_i' = ρ_o + D'`, and
`D'^{-7} + D'^{-6} ≤ 2 b^9 |x_obs'|^{-5}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIIa

private theorem mf_tn_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ tensorNorm M := by
  unfold tensorNorm; exact Real.sqrt_nonneg _

private theorem mf_thinMoment_eq (c : ℝ) (hc : 0 < c) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) :
    IIIa.thinMoment c (meanLift G) = ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (1 + |w.2|) *
      ENNReal.ofReal (tensorNorm (G w.1 w.2)) := by
  unfold IIIa.thinMoment IIIa.meanLift
  refine lintegral_congr fun w => ?_
  congr 1
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_assoc,
    mul_comm (ENNReal.ofReal _) (ENNReal.ofReal c), ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le),
    inv_mul_cancel₀ hc.ne']
  simp only [ENNReal.ofReal_one, one_mul]
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)]
  congr 1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (mf_tn_nonneg _)]

private theorem mf_pow_far (ρo ρi r b : ℝ) (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (hr : ρi ≤ r)
    (hb1 : 1 ≤ b) (hbi : ρi⁻¹ ≤ b) (hbA : ρi * (ρi - ρo)⁻¹ ≤ b) :
    ((ρi - ρo) * r / ρi) ^ (-7 : ℝ) + ((ρi - ρo) * r / ρi) ^ (-6 : ℝ) ≤
      2 * b ^ 9 * r ^ (-5 : ℝ) := by
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hD : 0 < ρi - ρo := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le hρi hr
  have hDp : 0 < (ρi - ρo) * r / ρi := by positivity
  have hx : r⁻¹ ≤ b := (inv_anti₀ hρi hr).trans hbi
  have hx0 : 0 ≤ r⁻¹ := inv_nonneg.2 hr0.le
  have hA0 : 0 ≤ ρi * (ρi - ρo)⁻¹ := by positivity
  have hinv : ((ρi - ρo) * r / ρi)⁻¹ = (ρi * (ρi - ρo)⁻¹) * r⁻¹ := by
    field_simp
  have e7 : ((ρi - ρo) * r / ρi) ^ (-7 : ℝ) = (((ρi - ρo) * r / ρi)⁻¹) ^ 7 := by
    rw [Real.rpow_neg hDp.le, show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  have e6 : ((ρi - ρo) * r / ρi) ^ (-6 : ℝ) = (((ρi - ρo) * r / ρi)⁻¹) ^ 6 := by
    rw [Real.rpow_neg hDp.le, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  have e5 : r ^ (-5 : ℝ) = (r⁻¹) ^ 5 := by
    rw [Real.rpow_neg hr0.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  rw [e7, e6, e5, hinv, mul_pow, mul_pow]
  have hb0 : 0 ≤ b := by linarith
  have h5 : 0 ≤ (r⁻¹) ^ 5 := by positivity
  have hA7 : (ρi * (ρi - ρo)⁻¹) ^ 7 ≤ b ^ 7 := pow_le_pow_left₀ hA0 hbA 7
  have hA6 : (ρi * (ρi - ρo)⁻¹) ^ 6 ≤ b ^ 6 := pow_le_pow_left₀ hA0 hbA 6
  have hx2 : (r⁻¹) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have hb69 : b ^ 6 * b ≤ b ^ 9 := by
    calc b ^ 6 * b = b ^ 7 := by ring
      _ ≤ b ^ 9 := pow_le_pow_right₀ hb1 (by norm_num)
  have t7 : (ρi * (ρi - ρo)⁻¹) ^ 7 * (r⁻¹) ^ 7 ≤ b ^ 9 * (r⁻¹) ^ 5 := by
    calc (ρi * (ρi - ρo)⁻¹) ^ 7 * (r⁻¹) ^ 7
        = (ρi * (ρi - ρo)⁻¹) ^ 7 * (r⁻¹) ^ 2 * (r⁻¹) ^ 5 := by ring
      _ ≤ b ^ 7 * b ^ 2 * (r⁻¹) ^ 5 := by gcongr
      _ = b ^ 9 * (r⁻¹) ^ 5 := by ring
  have t6 : (ρi * (ρi - ρo)⁻¹) ^ 6 * (r⁻¹) ^ 6 ≤ b ^ 9 * (r⁻¹) ^ 5 := by
    calc (ρi * (ρi - ρo)⁻¹) ^ 6 * (r⁻¹) ^ 6
        = (ρi * (ρi - ρo)⁻¹) ^ 6 * r⁻¹ * (r⁻¹) ^ 5 := by ring
      _ ≤ b ^ 6 * b * (r⁻¹) ^ 5 := by gcongr
      _ ≤ b ^ 9 * (r⁻¹) ^ 5 := by gcongr
  linarith

theorem sepMeanFar : SepMeanFar := by
  intro K hK hKre
  have hSK := sepKernelBounds
  obtain ⟨C0, hC0, hdiff⟩ := mp_diff_pointwise hSK
  refine ⟨2 * C0 + 1, 9, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ G hGm hGs xo hxo
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hD : 0 < ρi - ρo := by linarith
  have hDinv : 0 < (ρi - ρo)⁻¹ := inv_pos.2 hD
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := ⟨_, rfl⟩
  rw [← hrdef] at hxo ⊢
  have hr0 : 0 < r := lt_of_lt_of_le hρi hxo
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹ := ⟨_, rfl⟩
  rw [← hb]
  have hb1 : 1 ≤ b := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < ρi⁻¹ := inv_pos.2 hρi
    have : 0 < ρi * (ρi - ρo)⁻¹ := by positivity
    linarith
  have hbi : ρi⁻¹ ≤ b := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < ρi * (ρi - ρo)⁻¹ := by positivity
    linarith
  have hbA : ρi * (ρi - ρo)⁻¹ ≤ b := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < ρi⁻¹ := inv_pos.2 hρi
    linarith
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hCpos : 0 < (2 * C0 + 1) * b ^ 9 * ε ^ 4 * r ^ (-5 : ℝ) := by
    have : 0 < r ^ (-5 : ℝ) := Real.rpow_pos_of_pos hr0 _
    positivity
  by_cases hN : IIIa.thinMoment c (meanLift G) = ⊤
  · rw [hN, ENNReal.mul_top]
    · exact le_top
    · simpa using hCpos
  -- the sharper receiver gap
  obtain ⟨ρi', hρi'⟩ : ∃ ρi' : ℝ, ρi' = ρo + (ρi - ρo) * r / ρi := ⟨_, rfl⟩
  have hDp : ρi' - ρo = (ρi - ρo) * r / ρi := by rw [hρi']; ring
  have hDp0 : 0 < (ρi - ρo) * r / ρi := by positivity
  have hρ' : ρo < ρi' := by linarith
  have hxo' : ρi' ≤ r := by
    rw [hρi']
    have h1 : (ρi - ρo) * r / ρi = r - ρo * r / ρi := by field_simp
    have h2 : ρo ≤ ρo * r / ρi := by
      rw [le_div_iff₀ hρi]
      exact mul_le_mul_of_nonneg_left hxo hρo
    linarith
  -- integrability of the moment
  rw [mf_thinMoment_eq c hc G] at hN ⊢
  have hmeas : Measurable fun w : (ℝ × ℝ) × ℝ => tensorNorm (G w.1 w.2) := by
    unfold tensorNorm
    exact Measurable.sqrt (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => (hGm i j).pow_const 2)
  have hwm : Measurable fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * tensorNorm (G w.1 w.2) :=
    (measurable_const.add (continuous_abs.measurable.comp measurable_snd)).mul hmeas
  have hwint : Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * tensorNorm (G w.1 w.2)) volume := by
    refine ⟨hwm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ w : (ℝ × ℝ) × ℝ, ‖(1 + |w.2|) * tensorNorm (G w.1 w.2)‖ₑ =
        ENNReal.ofReal (1 + |w.2|) * ENNReal.ofReal (tensorNorm (G w.1 w.2)) := by
      intro w
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (mul_nonneg (by positivity) (mf_tn_nonneg _)),
        ENNReal.ofReal_mul (by positivity)]
    simp_rw [this]
    exact lt_top_iff_ne_top.2 hN
  have hint : Integrable (fun w : (ℝ × ℝ) × ℝ => tensorNorm (G w.1 w.2)) volume := by
    refine Integrable.mono' hwint hmeas.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_of_nonneg (mf_tn_nonneg _)]
    have : 0 ≤ tensorNorm (G w.1 w.2) := mf_tn_nonneg _
    exact le_mul_of_one_le_left this (by linarith [abs_nonneg w.2])
  obtain ⟨Nr, hNr⟩ : ∃ Nr : ℝ, Nr = ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * tensorNorm (G w.1 w.2) := ⟨_, rfl⟩
  have hNr0 : 0 ≤ Nr := by
    rw [hNr]; exact integral_nonneg fun w => mul_nonneg (by positivity) (mf_tn_nonneg _)
  have hNrE : ENNReal.ofReal Nr = ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (1 + |w.2|) *
      ENNReal.ofReal (tensorNorm (G w.1 w.2)) := by
    rw [hNr, ofReal_integral_eq_lintegral_ofReal hwint (Eventually.of_forall fun w =>
      mul_nonneg (by positivity) (mf_tn_nonneg _))]
    refine lintegral_congr fun w => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  rw [← hNrE]
  -- the two derivative formulas
  obtain ⟨hWd, hWf⟩ := mp_W_eval sepKernelBounds ν c ε ρo ρi μ hν hc hε hρo hρ (hKre μ hμ) G hGm hGs
    hint xo (hrdef ▸ hxo) 0
  obtain ⟨hVd, hVf⟩ := mp_V_deriv sepKernelBounds μ (hKre μ hμ) ρo ρi hρo hρ G hGm hGs hint xo (hrdef ▸ hxo)
  have hDD := mf_pow_far ρo ρi r b hρo hρ hxo hb1 hbi hbA
  rw [← hDp] at hDD
  have hCb : ∀ (v : Space) (i : Fin 3),
      ‖(fderiv ℝ (fun y => sepW ν μ (thinSource ε (meanLift G)) y 0) (ε⁻¹ • xo) -
          (ε ^ 3 : ℝ) • fderiv ℝ (sepVmu0 μ G) xo) v i‖ ≤
        (2 * C0 * b ^ 9 * ε ^ 4 * r ^ (-5 : ℝ) * Nr) * ‖v‖ := by
    intro v i
    obtain ⟨hWe, hWi⟩ := hWf v i
    obtain ⟨hVe, hVi⟩ := hVf v i
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, Pi.sub_apply,
      Pi.smul_apply]
    rw [hWe, hVe, Complex.real_smul]
    push_cast
    rw [← mul_sub, ← integral_sub hWi hVi, norm_mul]
    have hB : Integrable (fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
        (C0 * ε * ((ρi' - ρo) ^ (-7 : ℝ) + (ρi' - ρo) ^ (-6 : ℝ)) * ‖v‖) *
          ((1 + |p.2.2|) * tensorNorm (G p.2.1 p.2.2))) mpRho2 := by
      have h := (integrable_const (1 : ℝ) (μ := volume.restrict (Ioo (0 : ℝ) 1))).mul_prod hwint
      exact (h.congr (Eventually.of_forall fun p => by simp)).const_mul _
    have hnorm : ‖∫ p, (mpHW ν ε μ G xo v i p - mpVd μ G p xo v i) ∂mpRho2‖ ≤
        ∫ p, (C0 * ε * ((ρi' - ρo) ^ (-7 : ℝ) + (ρi' - ρo) ^ (-6 : ℝ)) * ‖v‖) *
          ((1 + |p.2.2|) * tensorNorm (G p.2.1 p.2.2)) ∂mpRho2 := by
      refine norm_integral_le_of_norm_le hB ?_
      filter_upwards [mpRho2_ae_mem] with p hp
      have := hdiff ν ε μ ρo ρi' hν hν1 hε hε1 (hKre μ hμ) hρo hρ' G hGs xo (hrdef ▸ hxo') v i p hp
      calc _ ≤ _ := this
        _ = _ := by ring
    have hI : ∫ p, (C0 * ε * ((ρi' - ρo) ^ (-7 : ℝ) + (ρi' - ρo) ^ (-6 : ℝ)) * ‖v‖) *
        ((1 + |p.2.2|) * tensorNorm (G p.2.1 p.2.2)) ∂mpRho2 =
        (C0 * ε * ((ρi' - ρo) ^ (-7 : ℝ) + (ρi' - ρo) ^ (-6 : ℝ)) * ‖v‖) * Nr := by
      rw [integral_const_mul]
      congr 1
      have := integral_prod_mul (μ := volume.restrict (Ioo (0 : ℝ) 1)) (ν := (volume : Measure ((ℝ × ℝ) × ℝ)))
        (fun _ => (1 : ℝ)) (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * tensorNorm (G w.1 w.2))
      simp only [one_mul, integral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
        smul_eq_mul] at this
      unfold mpRho2
      rw [hNr]
      simpa using this
    have hpow : ‖(ε : ℂ) ^ 3‖ = ε ^ 3 := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le]
    rw [hpow]
    calc ε ^ 3 * ‖∫ p, (mpHW ν ε μ G xo v i p - mpVd μ G p xo v i) ∂mpRho2‖
        ≤ ε ^ 3 * ((C0 * ε * ((ρi' - ρo) ^ (-7 : ℝ) + (ρi' - ρo) ^ (-6 : ℝ)) * ‖v‖) * Nr) := by
          rw [← hI]; gcongr
      _ ≤ ε ^ 3 * ((C0 * ε * (2 * b ^ 9 * r ^ (-5 : ℝ)) * ‖v‖) * Nr) := by gcongr
      _ = _ := by ring
  have hLn : ‖fderiv ℝ (fun y => sepW ν μ (thinSource ε (meanLift G)) y 0) (ε⁻¹ • xo) -
      (ε ^ 3 : ℝ) • fderiv ℝ (sepVmu0 μ G) xo‖ ≤ 2 * C0 * b ^ 9 * ε ^ 4 * r ^ (-5 : ℝ) * Nr := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    exact hCb v i
  rw [← ofReal_norm_eq_enorm]
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal (2 * C0 * b ^ 9 * ε ^ 4 * r ^ (-5 : ℝ) * Nr) :=
        ENNReal.ofReal_le_ofReal hLn
    _ ≤ ENNReal.ofReal ((2 * C0 + 1) * b ^ 9 * ε ^ 4 * r ^ (-5 : ℝ) * Nr) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : 0 ≤ r ^ (-5 : ℝ) := Real.rpow_nonneg hr0.le _
        have : 0 ≤ b := le_trans zero_le_one hb1
        gcongr
        linarith
    _ = ENNReal.ofReal ((2 * C0 + 1) * b ^ 9 * ε ^ 4 * r ^ (-5 : ℝ)) * ENNReal.ofReal Nr := by
        rw [ENNReal.ofReal_mul hCpos.le]

end UnforcedLeray.Short.PartIIIb.Concrete
