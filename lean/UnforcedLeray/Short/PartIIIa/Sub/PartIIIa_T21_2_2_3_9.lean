import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_8

/-!
# Helpers for `PartIII-a:T21/2/2/3/9`: the bound of the `E_1` rate

Source: `the November 2 reference manuscript`, lines 3062-3071 ("the diffusion-weight
errors have coefficient `C_m β` and the transport and compact terms have coefficient `C_b`"),
3044-3051.

* `WB`: the bounds on `w = p_d⁻¹` from `PeriodicWeightLogBounds` (`|∇w| ≤ C w`, `|y·∇w| ≤ C w`,
  `|∂_ζ w| ≤ (C/2) w` on the cell).
* `tk_gen`: for one `k`, `T_k + β Σ_l ∫ w|∂_l∂_kΦ|² ≤ c N_k + C_V (N_0 + N_1) + X_k`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

/-! ## The weight in the cell length -/

theorem pw_hasDerivAt_d (m d : ℝ) (hd : d ≠ 0) (y : ℝ × ℝ) :
    HasDerivAt (fun d' => periodicWeight m d' y)
      (WLB.DQ d y * m * WLB.Qf d y ^ (m - 1)) d :=
  (WLB.Qf_d d hd y).rpow_const (Or.inl (WLB.Qf_pos d y).ne')

theorem dtW_cont (m d β : ℝ) (hd : d ≠ 0) : Continuous (dtW m d β) := by
  have h : dtW m d β =
      fun y => WLB.DQ d y * (-m) * WLB.Qf d y ^ (-m - 1) * (d * β / 2) := by
    funext y
    unfold dtW
    rw [(pw_hasDerivAt_d (-m) d hd y).deriv]
  rw [h]
  have hDQ : Continuous (fun y : ℝ × ℝ => WLB.DQ d y) := by unfold WLB.DQ; fun_prop
  have hQ : Continuous (fun y : ℝ × ℝ => WLB.Qf d y) := by unfold WLB.Qf; fun_prop
  exact ((hDQ.mul continuous_const).mul
    (hQ.rpow_const (fun y => Or.inl (WLB.Qf_pos d y).ne'))).mul continuous_const

/-- The bounds on the periodic weight `w = p_d⁻¹` used for the `E_1` rate. -/
structure WB (m d β CW : ℝ) : Prop where
  grad : ∀ (y : ℝ × ℝ) (l : Fin 2),
    |B0579.pd l (periodicWeight (-m) d) y| ≤ CW * periodicWeight (-m) d y
  dil : ∀ y ∈ B0579.cell d,
    |y.1 * B0579.pd 0 (periodicWeight (-m) d) y + y.2 * B0579.pd 1 (periodicWeight (-m) d) y| ≤
      CW * periodicWeight (-m) d y
  dt : ∀ y ∈ B0579.cell d, |dtW m d β y| ≤ CW / 2 * periodicWeight (-m) d y
  dtc : Continuous (dtW m d β)

theorem wb_of_hW (hW : UnforcedLeray.Short.IIIa.PeriodicWeightLogBounds) (m : ℝ) :
    ∃ CW : ℝ, 0 ≤ CW ∧ ∀ d β : ℝ, 0 < d → 0 < β → β ≤ 1 → WB m d β CW := by
  obtain ⟨CW, hCW⟩ := hW (-m)
  have h0 : 0 ≤ CW := (abs_nonneg _).trans ((hCW 1 one_pos).1 0 0)
  refine ⟨CW, h0, fun d β hd hβ hβ1 => ?_⟩
  obtain ⟨h1, -, h3, h4⟩ := hCW d hd
  refine ⟨fun y l => pw_pd_abs_le (-m) d CW h1 l y, ?_, ?_, dtW_cont m d β hd.ne'⟩
  · intro y hy
    have e : y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
        y.2 * B0579.pd 1 (periodicWeight (-m) d) y =
        periodicWeight (-m) d y *
          (y.1 * B0579.pd 0 (fun x => Real.log (periodicWeight (-m) d x)) y +
            y.2 * B0579.pd 1 (fun x => Real.log (periodicWeight (-m) d x)) y) := by
      rw [pw_pd_eq (-m) d 0 y, pw_pd_eq (-m) d 1 y]; ring
    rw [e, abs_mul, abs_of_pos (pw_pos _ _ y), mul_comm]
    exact mul_le_mul_of_nonneg_right (h3 y hy) (pw_pos _ _ y).le
  · intro y hy
    have hp := pw_pos (-m) d y
    have hdl := (pw_hasDerivAt_d (-m) d hd.ne' y).log hp.ne'
    have hl : deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d =
        (WLB.DQ d y * (-m) * WLB.Qf d y ^ (-m - 1)) / periodicWeight (-m) d y := hdl.deriv
    have hw' : deriv (fun d' => periodicWeight (-m) d' y) d =
        WLB.DQ d y * (-m) * WLB.Qf d y ^ (-m - 1) := (pw_hasDerivAt_d (-m) d hd.ne' y).deriv
    have e : deriv (fun d' => periodicWeight (-m) d' y) d =
        periodicWeight (-m) d y * deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d := by
      have hne := hp.ne'
      rw [hl, hw']; field_simp
    have hb := h4 y hy
    have e2 : dtW m d β y = periodicWeight (-m) d y *
        (d * deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d) * (β / 2) := by
      unfold dtW
      rw [e]; ring
    rw [e2, abs_mul, abs_mul, abs_of_pos hp, abs_of_pos (by linarith : 0 < β / 2)]
    have h5 : periodicWeight (-m) d y *
        |d * deriv (fun d' => Real.log (periodicWeight (-m) d' y)) d| * (β / 2) ≤
        periodicWeight (-m) d y * CW * (β / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp.le) (by linarith)
    have h6 : periodicWeight (-m) d y * CW * (β / 2) ≤ periodicWeight (-m) d y * CW * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hp.le h0)
    linarith

/-! ## Real-variable inequalities -/

theorem young1 (w a c x : ℝ) (hw : 0 ≤ w) (hx : |x| ≤ a * c) :
    |w * x| ≤ 1 / 2 * (w * a ^ 2) + 1 / 2 * (w * c ^ 2) ∧
      -2 * (w * x) ≤ w * a ^ 2 + w * c ^ 2 := by
  have h1 : |w * x| ≤ w * (a * c) := by
    rw [abs_mul, abs_of_nonneg hw]; exact mul_le_mul_of_nonneg_left hx hw
  have h2 : w * (a * c) ≤ 1 / 2 * (w * a ^ 2) + 1 / 2 * (w * c ^ 2) := by
    nlinarith [mul_nonneg hw (sq_nonneg (a - c))]
  refine ⟨h1.trans h2, ?_⟩
  have h3 := le_abs_self (-(w * x))
  rw [abs_neg] at h3
  linarith

theorem cross_pt (g z w a b K : ℝ) (hw : 0 ≤ w) (hK : 0 ≤ K) (hg : |g| ≤ K * w)
    (hz : |z| ≤ a * b) : -(w * b ^ 2) - 2 * (g * z) ≤ K ^ 2 * (w * a ^ 2) := by
  have h1 : -(g * z) ≤ |g * z| := by
    have := le_abs_self (-(g * z))
    rwa [abs_neg] at this
  have h2 : |g * z| = |g| * |z| := abs_mul _ _
  have h3 : |g| * |z| ≤ (K * w) * (a * b) :=
    mul_le_mul hg hz (abs_nonneg _) (mul_nonneg hK hw)
  nlinarith [mul_nonneg hw (sq_nonneg (b - K * a))]

theorem dt_pt (w a a0 a1 CV x : ℝ) (hw : 0 ≤ w) (hCV : 0 ≤ CV)
    (hx : |x| ≤ a * (CV * a0 + CV * a1)) :
    |w * x| ≤ CV * (w * a ^ 2) + CV / 2 * (w * a0 ^ 2) + CV / 2 * (w * a1 ^ 2) ∧
      2 * (w * x) ≤ (2 * CV) * (w * a ^ 2) + CV * (w * a0 ^ 2) + CV * (w * a1 ^ 2) := by
  have h1 : |w * x| ≤ w * (a * (CV * a0 + CV * a1)) := by
    rw [abs_mul, abs_of_nonneg hw]; exact mul_le_mul_of_nonneg_left hx hw
  have e0 : a * a0 ≤ (a ^ 2 + a0 ^ 2) / 2 := by nlinarith [sq_nonneg (a - a0)]
  have e1 : a * a1 ≤ (a ^ 2 + a1 ^ 2) / 2 := by nlinarith [sq_nonneg (a - a1)]
  have h2 : w * (a * (CV * a0 + CV * a1)) ≤
      CV * (w * a ^ 2) + CV / 2 * (w * a0 ^ 2) + CV / 2 * (w * a1 ^ 2) := by
    have hwc : 0 ≤ w * CV := mul_nonneg hw hCV
    have := mul_le_mul_of_nonneg_left (add_le_add e0 e1) hwc
    nlinarith [this]
  have h3 := le_abs_self (w * x)
  constructor
  · exact h1.trans h2
  · nlinarith [h1, h2, h3]

theorem abs_re_conj_le (z v : ℂ) : |(starRingEnd ℂ z * v).re| ≤ ‖z‖ * ‖v‖ := by
  calc |(starRingEnd ℂ z * v).re| ≤ ‖starRingEnd ℂ z * v‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ * ‖v‖ := by rw [norm_mul, Complex.norm_conj]

theorem re_conj_self (u : ℂ) : (starRingEnd ℂ u * u).re = ‖u‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re] <;> ring

theorem xi_split (z L u T Dt X : ℂ) (β : ℝ) (hz : z = starRingEnd ℂ u) :
    (z * ((β : ℂ) * (L + (1 / 2 : ℂ) * u) + T + Dt - X)).re =
      β * (z * L).re + β / 2 * ‖u‖ ^ 2 + (z * T).re + (z * Dt).re - (z * X).re := by
  have hzu : (z * u).re = ‖u‖ ^ 2 := by rw [hz]; exact re_conj_self u
  have e : z * ((β : ℂ) * (L + (1 / 2 : ℂ) * u) + T + Dt - X) =
      (β : ℂ) * (z * L) + ((β / 2 : ℝ) : ℂ) * (z * u) + z * T + z * Dt - z * X := by
    push_cast; ring
  rw [e]
  simp only [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, hzu]

/-! ## Integral helpers -/

theorem intOn_of_abs_le {S : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ} (hS : MeasurableSet S)
    (hg : IntegrableOn g S) (hf : Continuous f) (h : ∀ y ∈ S, |f y| ≤ g y) :
    IntegrableOn f S :=
  Integrable.mono' hg hf.aestronglyMeasurable
    (ae_restrict_of_forall_mem hS fun y hy => by rw [Real.norm_eq_abs]; exact h y hy)

theorem bd {S : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ} {c : ℝ} (hS : MeasurableSet S)
    (hg : IntegrableOn g S) (hf : Continuous f) (h : ∀ y ∈ S, |f y| ≤ c * g y) :
    IntegrableOn f S ∧ |∫ y in S, f y| ≤ c * ∫ y in S, g y := by
  refine ⟨intOn_of_abs_le hS (hg.const_mul c) hf h, ?_⟩
  have := norm_integral_le_of_norm_le (hg.const_mul c)
    (ae_restrict_of_forall_mem hS fun y hy => by rw [Real.norm_eq_abs]; exact h y hy)
  rwa [integral_const_mul, Real.norm_eq_abs] at this

theorem integral_lin5 {S : Set (ℝ × ℝ)} {f1 f2 f3 f4 f5 : ℝ × ℝ → ℝ} (h1 : IntegrableOn f1 S)
    (h2 : IntegrableOn f2 S) (h3 : IntegrableOn f3 S) (h4 : IntegrableOn f4 S)
    (h5 : IntegrableOn f5 S) (a b : ℝ) :
    ∫ y in S, (a * f1 y + b * f2 y + f3 y + f4 y - f5 y) =
      a * (∫ y in S, f1 y) + b * (∫ y in S, f2 y) + (∫ y in S, f3 y) + (∫ y in S, f4 y) -
        (∫ y in S, f5 y) := by
  have i1 : Integrable (fun y => a * f1 y) (volume.restrict S) := h1.const_mul a
  have i2 : Integrable (fun y => b * f2 y) (volume.restrict S) := h2.const_mul b
  have i12 : Integrable (fun y => a * f1 y + b * f2 y) (volume.restrict S) := i1.add i2
  have i123 : Integrable (fun y => a * f1 y + b * f2 y + f3 y) (volume.restrict S) :=
    i12.add h3
  have i1234 : Integrable (fun y => a * f1 y + b * f2 y + f3 y + f4 y) (volume.restrict S) :=
    i123.add h4
  rw [integral_sub i1234 h5, integral_add i123 h4, integral_add i12 h3, integral_add i1 i2,
    integral_const_mul, integral_const_mul]

theorem integral_lin3 {S : Set (ℝ × ℝ)} {f1 f2 f3 : ℝ × ℝ → ℝ} (h1 : IntegrableOn f1 S)
    (h2 : IntegrableOn f2 S) (h3 : IntegrableOn f3 S) (a b c : ℝ) :
    ∫ y in S, (a * f1 y + b * f2 y + c * f3 y) =
      a * (∫ y in S, f1 y) + b * (∫ y in S, f2 y) + c * (∫ y in S, f3 y) := by
  have i1 : Integrable (fun y => a * f1 y) (volume.restrict S) := h1.const_mul a
  have i2 : Integrable (fun y => b * f2 y) (volume.restrict S) := h2.const_mul b
  have i3 : Integrable (fun y => c * f3 y) (volume.restrict S) := h3.const_mul c
  have i12 : Integrable (fun y => a * f1 y + b * f2 y) (volume.restrict S) := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-! ## The bound for one direction `k` -/

theorem norm_dT_le {V : ℝ × ℝ → Fin 2 → ℝ} {CV : ℝ} (hV : ContDiff ℝ 1 V)
    (hVb : ∀ j : ℕ, j ≤ 1 → ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j V y‖ ≤ CV) (Φ : ℝ × ℝ → ℂ)
    (k : Fin 2) (y : ℝ × ℝ) :
    ‖dTransC V Φ k y‖ ≤ CV * ‖pdCx 0 Φ y‖ + CV * ‖pdCx 1 Φ y‖ := by
  unfold dTransC
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (pdV_abs_le hV hVb y k 0) (norm_nonneg _)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (pdV_abs_le hV hVb y k 1) (norm_nonneg _)

theorem tk_gen (d β CW CV : ℝ) (w D : ℝ × ℝ → ℝ) (V : ℝ × ℝ → Fin 2 → ℝ)
    (Φ χ : ℝ × ℝ → ℂ) (k : Fin 2) (hβ : 0 < β) (hβ1 : β ≤ 1) (hCW : 0 ≤ CW) (hCV : 0 ≤ CV)
    (hw : ContDiff ℝ 1 w) (hw0 : ∀ y, 0 ≤ w y)
    (hgrad : ∀ (y : ℝ × ℝ) (l : Fin 2), |B0579.pd l w y| ≤ CW * w y)
    (hdil : ∀ y ∈ B0579.cell d, |y.1 * B0579.pd 0 w y + y.2 * B0579.pd 1 w y| ≤ CW * w y)
    (hD : ∀ y ∈ B0579.cell d, |D y| ≤ CW / 2 * w y) (hDc : Continuous D)
    (hV : ContDiff ℝ 1 V)
    (hVb : ∀ j : ℕ, j ≤ 1 → ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j V y‖ ≤ CV)
    (hΦ : ContDiff ℝ ∞ Φ) (hχ : ContDiff ℝ 1 χ)
    (iN : ∀ l : Fin 2, IntegrableOn (fun y => w y * ‖pdCx l Φ y‖ ^ 2) (B0579.cell d))
    (iS : ∀ l : Fin 2,
      IntegrableOn (fun y => w y * ‖pdCx l (pdCx k Φ) y‖ ^ 2) (B0579.cell d))
    (iX : IntegrableOn (fun y => w y * ‖pdCx k χ y‖ ^ 2) (B0579.cell d))
    (hLap : IntegrableOn (fun y => w y *
        ((starRingEnd ℂ) (pdCx k Φ y) * lapC (pdCx k Φ) y).re) (B0579.cell d) ∧
      (∀ l : Fin 2, IntegrableOn (fun y => B0579.pd l w y *
        ((starRingEnd ℂ) (pdCx k Φ y) * pdCx l (pdCx k Φ) y).re) (B0579.cell d)) ∧
      ∫ y in B0579.cell d, w y *
          ((starRingEnd ℂ) (pdCx k Φ y) * lapC (pdCx k Φ) y).re =
        -(∑ l : Fin 2, ∫ y in B0579.cell d, w y * ‖pdCx l (pdCx k Φ) y‖ ^ 2) -
          ∑ l : Fin 2, ∫ y in B0579.cell d, B0579.pd l w y *
            ((starRingEnd ℂ) (pdCx k Φ y) * pdCx l (pdCx k Φ) y).re)
    (hTrn : IntegrableOn (fun y => w y *
        ((starRingEnd ℂ) (pdCx k Φ y) * transC V (pdCx k Φ) y).re) (B0579.cell d) ∧
      IntegrableOn (fun y => (V y 0 * B0579.pd 0 w y +
          V y 1 * B0579.pd 1 w y + w y *
            (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) *
          ‖pdCx k Φ y‖ ^ 2) (B0579.cell d) ∧
      2 * ∫ y in B0579.cell d, w y *
          ((starRingEnd ℂ) (pdCx k Φ y) * transC V (pdCx k Φ) y).re =
        -∫ y in B0579.cell d, (V y 0 * B0579.pd 0 w y +
          V y 1 * B0579.pd 1 w y + w y *
            (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) *
          ‖pdCx k Φ y‖ ^ 2) :
    (∫ y in B0579.cell d, D y * ‖pdCx k Φ y‖ ^ 2) +
      2 * (∫ y in B0579.cell d,
        w y * ((starRingEnd ℂ) (pdCx k Φ y) * xiRed β V Φ χ k y).re) +
      β / 2 * (∫ y in B0579.cell d,
        (2 * w y + (y.1 * B0579.pd 0 w y + y.2 * B0579.pd 1 w y)) * ‖pdCx k Φ y‖ ^ 2) +
      β * (∑ l : Fin 2, ∫ y in B0579.cell d, w y * ‖pdCx l (pdCx k Φ) y‖ ^ 2) ≤
    (CW + 2 * CW ^ 2 + 3 + 2 * CV * CW + 4 * CV) *
        (∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) +
      CV * ((∫ y in B0579.cell d, w y * ‖pdCx 0 Φ y‖ ^ 2) +
        ∫ y in B0579.cell d, w y * ‖pdCx 1 Φ y‖ ^ 2) +
      ∫ y in B0579.cell d, w y * ‖pdCx k χ y‖ ^ 2 := by
  obtain ⟨iLap, iCr, eLap⟩ := hLap
  obtain ⟨iTr, iA, eTr⟩ := hTrn
  have hS : MeasurableSet (B0579.cell d) := B0579.measurableSet_cell d
  have hu : ContDiff ℝ ∞ (pdCx k Φ) := pdCx_contDiff hΦ k
  have huc : Continuous (pdCx k Φ) := hu.continuous
  have hu1 : ∀ l, Continuous (pdCx l Φ) := fun l => (pdCx_contDiff hΦ l).continuous
  have hwc : Continuous w := hw.continuous
  have hpw : ∀ l, Continuous (B0579.pd l w) := fun l => pdContinuous hw l
  have hχk : Continuous (pdCx k χ) := by
    unfold pdCx
    exact (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hVc : Continuous V := hV.continuous
  have hV0 : Continuous (fun y => V y 0) := (continuous_apply 0).comp hVc
  have hV1 : Continuous (fun y => V y 1) := (continuous_apply 1).comp hVc
  have hpV : ∀ k' j : Fin 2, Continuous (B0579.pd k' (fun x => V x j)) := fun k' j =>
    pdContinuous (contDiff_pi.1 hV j) k'
  have hnu : Continuous (fun y => ‖pdCx k Φ y‖ ^ 2) := huc.norm.pow 2
  have iNk := iN k
  have hNk : 0 ≤ ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2 :=
    setIntegral_nonneg hS fun y _ => mul_nonneg (hw0 y) (sq_nonneg _)
  -- (a) the weight derivative term
  have hI1 : ∫ y in B0579.cell d, D y * ‖pdCx k Φ y‖ ^ 2 ≤
      CW / 2 * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2 := by
    have := (bd (c := CW / 2) hS iNk (hDc.mul hnu) (fun y hy => by
      show |D y * ‖pdCx k Φ y‖ ^ 2| ≤ _
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖pdCx k Φ y‖)]
      calc |D y| * ‖pdCx k Φ y‖ ^ 2 ≤ CW / 2 * w y * ‖pdCx k Φ y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hD y hy) (sq_nonneg _)
        _ = _ := by ring)).2
    exact (le_abs_self _).trans this
  -- (b) the transport term
  have hIA : -(∫ y in B0579.cell d, (V y 0 * B0579.pd 0 w y +
          V y 1 * B0579.pd 1 w y + w y *
            (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) *
          ‖pdCx k Φ y‖ ^ 2) ≤
      (2 * CV * CW + 2 * CV) * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2 := by
    have hcA : Continuous (fun y => (V y 0 * B0579.pd 0 w y +
          V y 1 * B0579.pd 1 w y + w y *
            (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) *
          ‖pdCx k Φ y‖ ^ 2) :=
      (((hV0.mul (hpw 0)).add (hV1.mul (hpw 1))).add
        (hwc.mul ((hpV 0 0).add (hpV 1 1)))).mul hnu
    have := (bd (c := 2 * CV * CW + 2 * CV) hS iNk hcA (fun y _ => by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖pdCx k Φ y‖ ^ 2)]
      have hwy := hw0 y
      have b0 := V_abs_le hVb y 0
      have b1 := V_abs_le hVb y 1
      have g0 := hgrad y 0
      have g1 := hgrad y 1
      have d0 := pdV_abs_le hV hVb y 0 0
      have d1 := pdV_abs_le hV hVb y 1 1
      have t1 : |V y 0 * B0579.pd 0 w y| ≤ CV * (CW * w y) := by
        rw [abs_mul]; exact mul_le_mul b0 g0 (abs_nonneg _) hCV
      have t2 : |V y 1 * B0579.pd 1 w y| ≤ CV * (CW * w y) := by
        rw [abs_mul]; exact mul_le_mul b1 g1 (abs_nonneg _) hCV
      have t3 : |w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)| ≤
          w y * (2 * CV) := by
        rw [abs_mul, abs_of_nonneg hwy]
        exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by linarith)) hwy
      have hsum : |V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y +
            w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)| ≤
          (2 * CV * CW + 2 * CV) * w y := by
        refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
        nlinarith
      calc _ ≤ (2 * CV * CW + 2 * CV) * w y * ‖pdCx k Φ y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
        _ = _ := by ring)).2
    have h2 := le_abs_self (-(∫ y in B0579.cell d, (V y 0 * B0579.pd 0 w y +
          V y 1 * B0579.pd 1 w y + w y *
            (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) *
          ‖pdCx k Φ y‖ ^ 2))
    rw [abs_neg] at h2
    linarith
  -- (c) the cross terms
  have hcr : ∀ l : Fin 2, -(∫ y in B0579.cell d, w y * ‖pdCx l (pdCx k Φ) y‖ ^ 2) -
      2 * (∫ y in B0579.cell d, B0579.pd l w y *
        ((starRingEnd ℂ) (pdCx k Φ y) * pdCx l (pdCx k Φ) y).re) ≤
      CW ^ 2 * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2 := by
    intro l
    have iS' := iS l
    have iP' := iCr l
    have hf : IntegrableOn (fun y => -(w y * ‖pdCx l (pdCx k Φ) y‖ ^ 2) -
        2 * (B0579.pd l w y * ((starRingEnd ℂ) (pdCx k Φ y) * pdCx l (pdCx k Φ) y).re))
        (B0579.cell d) := iS'.neg.sub (iP'.const_mul 2)
    have hg : IntegrableOn (fun y => CW ^ 2 * (w y * ‖pdCx k Φ y‖ ^ 2)) (B0579.cell d) :=
      iNk.const_mul _
    have := setIntegral_mono_on hf hg hS (fun y _ =>
      cross_pt (B0579.pd l w y) _ (w y) ‖pdCx k Φ y‖ ‖pdCx l (pdCx k Φ) y‖ CW (hw0 y) hCW
        (hgrad y l) (abs_re_conj_le _ _))
    have iN2 : Integrable (fun y => -(w y * ‖pdCx l (pdCx k Φ) y‖ ^ 2))
        (volume.restrict (B0579.cell d)) := iS'.neg
    have iP2 : Integrable (fun y => 2 * (B0579.pd l w y *
        ((starRingEnd ℂ) (pdCx k Φ y) * pdCx l (pdCx k Φ) y).re))
        (volume.restrict (B0579.cell d)) := iP'.const_mul 2
    rw [integral_sub iN2 iP2, integral_neg, integral_const_mul,
      integral_const_mul] at this
    exact this
  -- (d) the derivative-of-velocity term
  have hdT : ∀ y : ℝ × ℝ, |(starRingEnd ℂ (pdCx k Φ y) * dTransC V Φ k y).re| ≤
      ‖pdCx k Φ y‖ * (CV * ‖pdCx 0 Φ y‖ + CV * ‖pdCx 1 Φ y‖) := fun y =>
    (abs_re_conj_le _ _).trans (mul_le_mul_of_nonneg_left (norm_dT_le hV hVb Φ k y)
      (norm_nonneg _))
  have hcdT : Continuous (fun y => w y *
      ((starRingEnd ℂ) (pdCx k Φ y) * dTransC V Φ k y).re) := by
    have hdt : Continuous (fun y => dTransC V Φ k y) := by
      unfold dTransC
      exact ((Complex.continuous_ofReal.comp (hpV k 0)).mul (hu1 0)).add
        ((Complex.continuous_ofReal.comp (hpV k 1)).mul (hu1 1))
    exact hwc.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp huc).mul hdt))
  have iNsum : IntegrableOn (fun y => CV * (w y * ‖pdCx k Φ y‖ ^ 2) +
      CV / 2 * (w y * ‖pdCx 0 Φ y‖ ^ 2) + CV / 2 * (w y * ‖pdCx 1 Φ y‖ ^ 2)) (B0579.cell d) :=
    ((iNk.const_mul CV).add ((iN 0).const_mul (CV / 2))).add ((iN 1).const_mul (CV / 2))
  have iPdT : IntegrableOn (fun y => w y *
      ((starRingEnd ℂ) (pdCx k Φ y) * dTransC V Φ k y).re) (B0579.cell d) :=
    intOn_of_abs_le hS iNsum hcdT (fun y _ =>
      (dt_pt (w y) ‖pdCx k Φ y‖ ‖pdCx 0 Φ y‖ ‖pdCx 1 Φ y‖ CV _ (hw0 y) hCV (hdT y)).1)
  have hJd : 2 * (∫ y in B0579.cell d, w y *
      ((starRingEnd ℂ) (pdCx k Φ y) * dTransC V Φ k y).re) ≤
      CV * (2 * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) +
        CV * (∫ y in B0579.cell d, w y * ‖pdCx 0 Φ y‖ ^ 2) +
        CV * ∫ y in B0579.cell d, w y * ‖pdCx 1 Φ y‖ ^ 2 := by
    have hg : IntegrableOn (fun y => (2 * CV) * (w y * ‖pdCx k Φ y‖ ^ 2) +
        CV * (w y * ‖pdCx 0 Φ y‖ ^ 2) + CV * (w y * ‖pdCx 1 Φ y‖ ^ 2)) (B0579.cell d) :=
      ((iNk.const_mul (2 * CV)).add ((iN 0).const_mul CV)).add ((iN 1).const_mul CV)
    have := setIntegral_mono_on (iPdT.const_mul 2) hg hS (fun y _ =>
      (dt_pt (w y) ‖pdCx k Φ y‖ ‖pdCx 0 Φ y‖ ‖pdCx 1 Φ y‖ CV _ (hw0 y) hCV (hdT y)).2)
    rw [integral_const_mul, integral_lin3 iNk (iN 0) (iN 1)] at this
    linarith
  -- (e) the interaction term
  have hcχ : Continuous (fun y => w y *
      ((starRingEnd ℂ) (pdCx k Φ y) * pdCx k χ y).re) :=
    hwc.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp huc).mul hχk))
  have iPχ : IntegrableOn (fun y => w y *
      ((starRingEnd ℂ) (pdCx k Φ y) * pdCx k χ y).re) (B0579.cell d) :=
    intOn_of_abs_le hS ((iNk.const_mul (1 / 2)).add (iX.const_mul (1 / 2))) hcχ (fun y _ =>
      (young1 (w y) ‖pdCx k Φ y‖ ‖pdCx k χ y‖ _ (hw0 y) (abs_re_conj_le _ _)).1)
  have hJc : -2 * (∫ y in B0579.cell d, w y *
      ((starRingEnd ℂ) (pdCx k Φ y) * pdCx k χ y).re) ≤
      (∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) +
        ∫ y in B0579.cell d, w y * ‖pdCx k χ y‖ ^ 2 := by
    have hg : IntegrableOn (fun y => w y * ‖pdCx k Φ y‖ ^ 2 + w y * ‖pdCx k χ y‖ ^ 2)
        (B0579.cell d) := iNk.add iX
    have := setIntegral_mono_on (iPχ.const_mul (-2)) hg hS (fun y _ =>
      (young1 (w y) ‖pdCx k Φ y‖ ‖pdCx k χ y‖ _ (hw0 y) (abs_re_conj_le _ _)).2)
    rw [integral_const_mul, integral_add iNk iX] at this
    exact this
  -- (f) the dilation term
  have hI3 : ∫ y in B0579.cell d,
      (2 * w y + (y.1 * B0579.pd 0 w y + y.2 * B0579.pd 1 w y)) * ‖pdCx k Φ y‖ ^ 2 ≤
      (2 + CW) * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2 := by
    have hc3 : Continuous (fun y : ℝ × ℝ => (2 * w y + (y.1 * B0579.pd 0 w y +
        y.2 * B0579.pd 1 w y)) * ‖pdCx k Φ y‖ ^ 2) :=
      ((continuous_const.mul hwc).add
        ((continuous_fst.mul (hpw 0)).add (continuous_snd.mul (hpw 1)))).mul hnu
    have := (bd (c := 2 + CW) hS iNk hc3 (fun y hy => by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖pdCx k Φ y‖ ^ 2)]
      have hwy := hw0 y
      have h1 := hdil y hy
      have h2 : |2 * w y + (y.1 * B0579.pd 0 w y + y.2 * B0579.pd 1 w y)| ≤
          (2 + CW) * w y := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two, abs_of_nonneg hwy]
        nlinarith
      calc _ ≤ (2 + CW) * w y * ‖pdCx k Φ y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = _ := by ring)).2
    exact (le_abs_self _).trans this
  -- (g) the splitting of the middle integral
  have hIx : ∫ y in B0579.cell d, w y *
      ((starRingEnd ℂ) (pdCx k Φ y) * xiRed β V Φ χ k y).re =
      β * (∫ y in B0579.cell d, w y *
          ((starRingEnd ℂ) (pdCx k Φ y) * lapC (pdCx k Φ) y).re) +
        β / 2 * (∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) +
        (∫ y in B0579.cell d, w y *
          ((starRingEnd ℂ) (pdCx k Φ y) * transC V (pdCx k Φ) y).re) +
        (∫ y in B0579.cell d, w y *
          ((starRingEnd ℂ) (pdCx k Φ y) * dTransC V Φ k y).re) -
        ∫ y in B0579.cell d, w y * ((starRingEnd ℂ) (pdCx k Φ y) * pdCx k χ y).re := by
    have hpt : ∀ y : ℝ × ℝ, w y * ((starRingEnd ℂ) (pdCx k Φ y) * xiRed β V Φ χ k y).re =
        β * (w y * ((starRingEnd ℂ) (pdCx k Φ y) * lapC (pdCx k Φ) y).re) +
          β / 2 * (w y * ‖pdCx k Φ y‖ ^ 2) +
          w y * ((starRingEnd ℂ) (pdCx k Φ y) * transC V (pdCx k Φ) y).re +
          w y * ((starRingEnd ℂ) (pdCx k Φ y) * dTransC V Φ k y).re -
          w y * ((starRingEnd ℂ) (pdCx k Φ y) * pdCx k χ y).re := by
      intro y
      unfold xiRed
      rw [xi_split _ _ _ _ _ _ β rfl]
      ring
    rw [setIntegral_congr_fun hS (fun y _ => hpt y)]
    exact integral_lin5 iLap iNk iTr iPdT iPχ β (β / 2)
  -- (h) assembly
  have hJl : β * (∫ y in B0579.cell d, w y *
        ((starRingEnd ℂ) (pdCx k Φ y) * lapC (pdCx k Φ) y).re) =
      β * (-(∑ l : Fin 2, ∫ y in B0579.cell d, w y * ‖pdCx l (pdCx k Φ) y‖ ^ 2) -
          ∑ l : Fin 2, ∫ y in B0579.cell d, B0579.pd l w y *
            ((starRingEnd ℂ) (pdCx k Φ y) * pdCx l (pdCx k Φ) y).re) := by
    rw [eLap]
  rw [hIx]
  simp only [Fin.sum_univ_two] at hJl ⊢
  have hc0 := hcr 0
  have hc1 := hcr 1
  have hβc : β * ((-(∫ y in B0579.cell d, w y * ‖pdCx 0 (pdCx k Φ) y‖ ^ 2) -
        2 * (∫ y in B0579.cell d, B0579.pd 0 w y *
          ((starRingEnd ℂ) (pdCx k Φ y) * pdCx 0 (pdCx k Φ) y).re)) +
      (-(∫ y in B0579.cell d, w y * ‖pdCx 1 (pdCx k Φ) y‖ ^ 2) -
        2 * (∫ y in B0579.cell d, B0579.pd 1 w y *
          ((starRingEnd ℂ) (pdCx k Φ y) * pdCx 1 (pdCx k Φ) y).re))) ≤
      β * (2 * CW ^ 2 * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hβ.le
  have hβd : β * (2 * CW ^ 2 * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) ≤
      1 * (2 * CW ^ 2 * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hβ1
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg CW)) hNk)
  have hβN : β * (∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) ≤
      1 * (∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hβ1 hNk
  have hβI : β / 2 * (∫ y in B0579.cell d,
      (2 * w y + (y.1 * B0579.pd 0 w y + y.2 * B0579.pd 1 w y)) * ‖pdCx k Φ y‖ ^ 2) ≤
      β / 2 * ((2 + CW) * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hI3 (by linarith)
  have hβI2 : β / 2 * ((2 + CW) * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) ≤
      1 / 2 * ((2 + CW) * ∫ y in B0579.cell d, w y * ‖pdCx k Φ y‖ ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by linarith) hNk)
  linarith [hI1, hIA, hJd, hJc, hβc, hβd, hβN, hβI, hβI2, eTr, hJl]

end UnforcedLeray.Short.IIIa.AdjE1
