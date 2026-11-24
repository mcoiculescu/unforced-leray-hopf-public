import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs

/-!
# Part III-a, `PartIII-a:T21/2/2/2/12`: the rate estimate `CellRateEstimate` (SP 3062-3066)

For `θ ≥ 1`, with `C = 2K + 4 + 2 C_V K + 2K² + C_X`,
`rate0Reduced + θ⁻¹ E_1 ≤ C E_0`. The proof splits the four terms of `rate0Reduced`:
the transport-and-weight term is bounded pointwise by `(2K + 3 + 2C_V K) w|Φ|²`, the cross term
`-2θ⁻¹ Σ_k ∫ ∂_k w Re(Φ̄∂_kΦ)` by `θ⁻¹ E_1 + 2K² E_0`, and the interaction term
`-2∫ w Re(Φ̄χ)` by `(1 + C_X) E_0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-! ## Continuity of the derivatives -/

theorem pdCx_continuous {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ 2 Φ) (k : Fin 2) :
    Continuous (pdCx k Φ) := by
  unfold pdCx
  exact (hΦ.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem pd_real_continuous {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (k : Fin 2) :
    Continuous (B0579.pd k f) := by
  unfold B0579.pd
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-! ## Pointwise inequalities -/

/-- The modulus of the transport-and-weight coefficient on the cell (all `θ ≥ 1`). -/
theorem abs_rate_bound (θ d K CV w D I g0 g1 v0 v1 : ℝ) (hθ : 1 ≤ θ) (hK : 0 ≤ K)
    (hCV : 0 ≤ CV) (hw : 0 ≤ w)
    (hD : |d * D| ≤ K * w) (hI : |I| ≤ K * w) (hg0 : |g0| ≤ K * w) (hg1 : |g1| ≤ K * w)
    (hv0 : |v0| ≤ CV) (hv1 : |v1| ≤ CV) :
    |d / (2 * θ) * D + 3 * θ⁻¹ * w + (2 * θ)⁻¹ * I - (v0 * g0 + v1 * g1)| ≤
      (2 * K + 3 + 2 * CV * K) * w := by
  have hθ0 : 0 < θ := by linarith
  have hi : θ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hθ
  have hi0 : 0 ≤ θ⁻¹ := (inv_pos.mpr hθ0).le
  have h2i : (2 * θ)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
  have h2i0 : 0 ≤ (2 * θ)⁻¹ := (inv_pos.mpr (by linarith)).le
  have hrw : d / (2 * θ) * D = (2 * θ)⁻¹ * (d * D) := by ring
  rw [hrw]
  have hT1 : |(2 * θ)⁻¹ * (d * D)| ≤ K * w := by
    rw [abs_mul, abs_of_nonneg h2i0]
    calc (2 * θ)⁻¹ * |d * D| ≤ 1 * |d * D| := mul_le_mul_of_nonneg_right h2i (abs_nonneg _)
      _ ≤ K * w := by rw [one_mul]; exact hD
  have hT3 : |(2 * θ)⁻¹ * I| ≤ K * w := by
    rw [abs_mul, abs_of_nonneg h2i0]
    calc (2 * θ)⁻¹ * |I| ≤ 1 * |I| := mul_le_mul_of_nonneg_right h2i (abs_nonneg _)
      _ ≤ K * w := by rw [one_mul]; exact hI
  have hT2a : 0 ≤ θ⁻¹ * w := mul_nonneg hi0 hw
  have hT2b : θ⁻¹ * w ≤ w := by
    calc θ⁻¹ * w ≤ 1 * w := mul_le_mul_of_nonneg_right hi hw
      _ = w := one_mul w
  have hb0 : |v0 * g0| ≤ CV * (K * w) := by
    rw [abs_mul]; exact mul_le_mul hv0 hg0 (abs_nonneg _) hCV
  have hb1 : |v1 * g1| ≤ CV * (K * w) := by
    rw [abs_mul]; exact mul_le_mul hv1 hg1 (abs_nonneg _) hCV
  have h1 := abs_le.mp hT1
  have h3 := abs_le.mp hT3
  have h4 := abs_le.mp hb0
  have h5 := abs_le.mp hb1
  apply abs_le.mpr
  constructor
  · nlinarith [h1.1, h3.1, h4.1, h5.1, hT2a, hw]
  · nlinarith [h1.2, h3.2, h4.2, h5.2, hT2b, hw]

/-- Cross term: `|-2 g z| ≤ w b² + K² w a²` when `|g| ≤ K w` and `|z| ≤ a b`. -/
theorem cross_pt (g z w a b K : ℝ) (hw : 0 ≤ w) (hK : 0 ≤ K) (hg : |g| ≤ K * w)
    (hz : |z| ≤ a * b) :
    -2 * (g * z) ≤ w * b ^ 2 + K ^ 2 * (w * a ^ 2) := by
  have h1 : -(g * z) ≤ |g * z| := by
    have := le_abs_self (-(g * z))
    rwa [abs_neg] at this
  have h2 : |g * z| = |g| * |z| := abs_mul _ _
  have h3 : |g| * |z| ≤ (K * w) * (a * b) :=
    mul_le_mul hg hz (abs_nonneg _) (mul_nonneg hK hw)
  nlinarith [mul_nonneg hw (sq_nonneg (b - K * a))]

theorem cross_abs (g z w a b K : ℝ) (hw : 0 ≤ w) (hK : 0 ≤ K) (hg : |g| ≤ K * w)
    (hz : |z| ≤ a * b) :
    |-2 * (g * z)| ≤ w * b ^ 2 + K ^ 2 * (w * a ^ 2) := by
  have hg' : |-g| ≤ K * w := by rw [abs_neg]; exact hg
  have hz' : |-z| ≤ a * b := by rw [abs_neg]; exact hz
  have p1 := cross_pt g z w a b K hw hK hg hz
  have p2 := cross_pt (-g) z w a b K hw hK hg' hz
  rw [abs_le]
  constructor
  · linarith [p1, p2]
  · linarith [p1, p2]

/-- Interaction term: `-2 w Re(Φ̄χ) ≤ w a² + w c²` when `|z| ≤ a c`. -/
theorem wRe_pt (z w a c : ℝ) (hw : 0 ≤ w) (hz : |z| ≤ a * c) :
    -2 * (w * z) ≤ w * a ^ 2 + w * c ^ 2 := by
  have h1 : -z ≤ |z| := by
    have := le_abs_self (-z)
    rwa [abs_neg] at this
  have h2 : w * (-z) ≤ w * |z| := mul_le_mul_of_nonneg_left h1 hw
  have h3 : w * |z| ≤ w * (a * c) := mul_le_mul_of_nonneg_left hz hw
  nlinarith [mul_nonneg hw (sq_nonneg (a - c))]

theorem wRe_abs (z w a c : ℝ) (hw : 0 ≤ w) (hz : |z| ≤ a * c) :
    |-2 * (w * z)| ≤ w * a ^ 2 + w * c ^ 2 := by
  have hz' : |-z| ≤ a * c := by rw [abs_neg]; exact hz
  have p1 := wRe_pt z w a c hw hz
  have p2 := wRe_pt (-z) w a c hw hz'
  rw [abs_le]
  constructor
  · linarith [p1, p2]
  · linarith [p1, p2]

theorem re_conj_bound (u v : ℂ) : |(starRingEnd ℂ u * v).re| ≤ ‖u‖ * ‖v‖ := by
  calc |(starRingEnd ℂ u * v).re| ≤ ‖starRingEnd ℂ u * v‖ := Complex.abs_re_le_norm _
    _ = ‖u‖ * ‖v‖ := by rw [norm_mul, Complex.norm_conj]

/-! ## The cross integral -/

/-- One direction `k` of the cross term: `-2∫ ∂_k w Re(Φ̄∂_kΦ) ≤ ∫ w|∂_kΦ|² + K² E_0`. -/
theorem cross_integral_bound (m d K : ℝ) (Φ : ℝ × ℝ → ℂ) (k : Fin 2) (hK : 0 ≤ K)
    (hwt : CellWeight d K (periodicWeight (-m) d)) (hΦ : CellField m d Φ) :
    -2 * (∫ y in B0579.cell d,
        B0579.pd k (periodicWeight (-m) d) y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re) ≤
      (∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) +
        K ^ 2 * adjE0 d m Φ := by
  have hcell : MeasurableSet (B0579.cell d) := B0579.measurableSet_cell d
  have hwS : ContDiff ℝ 1 (periodicWeight (-m) d) := hwt.smooth
  have hΦS : ContDiff ℝ 2 Φ := hΦ.smooth
  have hΦc : Continuous Φ := hΦS.continuous
  have hpk : Continuous (pdCx k Φ) := pdCx_continuous hΦS k
  have hpw : Continuous (B0579.pd k (periodicWeight (-m) d)) := pd_real_continuous hwS k
  have hI0 := hΦ.int0
  have hI1 := hΦ.int1 k
  have hAdd : Integrable (fun y => periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2 +
      K ^ 2 * (periodicWeight (-m) d y * ‖Φ y‖ ^ 2)) (volume.restrict (B0579.cell d)) :=
    hI1.add (hI0.const_mul (K ^ 2))
  have hcontF : Continuous (fun y => -2 *
      (B0579.pd k (periodicWeight (-m) d) y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re)) := by
    have hre : Continuous (fun y => (starRingEnd ℂ (Φ y) * pdCx k Φ y).re) :=
      Complex.continuous_re.comp ((Complex.continuous_conj.comp hΦc).mul hpk)
    exact continuous_const.mul (hpw.mul hre)
  have hF : Integrable (fun y => -2 *
      (B0579.pd k (periodicWeight (-m) d) y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re))
      (volume.restrict (B0579.cell d)) := by
    refine Integrable.mono' hAdd hcontF.aestronglyMeasurable
      (ae_restrict_of_forall_mem hcell (fun y _ => ?_))
    rw [Real.norm_eq_abs]
    exact cross_abs _ _ _ _ _ _ (hwt.nonneg y) hK (hwt.grad y k)
      (re_conj_bound (Φ y) (pdCx k Φ y))
  calc -2 * (∫ y in B0579.cell d,
        B0579.pd k (periodicWeight (-m) d) y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re)
      = ∫ y in B0579.cell d, -2 *
          (B0579.pd k (periodicWeight (-m) d) y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ y in B0579.cell d, (periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2 +
          K ^ 2 * (periodicWeight (-m) d y * ‖Φ y‖ ^ 2)) := by
        refine integral_mono_ae hF hAdd (ae_restrict_of_forall_mem hcell (fun y _ => ?_))
        exact (le_abs_self _).trans
          (cross_abs _ _ _ _ _ _ (hwt.nonneg y) hK (hwt.grad y k)
            (re_conj_bound (Φ y) (pdCx k Φ y)))
    _ = (∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) +
          K ^ 2 * adjE0 d m Φ := by
        rw [integral_add hI1 (hI0.const_mul (K ^ 2)), integral_const_mul]
        rfl

/-! ## The main estimate -/

theorem cellRateEstimate : UnforcedLeray.Short.IIIa.E0.CellRateEstimate := by
  unfold CellRateEstimate
  intro m K CV CX hK hCV hCX
  refine ⟨2 * K + 4 + 2 * CV * K + 2 * K ^ 2 + CX, ?_, ?_⟩
  · nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCV) hK, sq_nonneg K]
  intro d θ Φ χ V hd hθ hW hΦ hV hχm hχint hχb
  have hcell : MeasurableSet (B0579.cell d) := B0579.measurableSet_cell d
  have hwt := hW.base
  have hwS : ContDiff ℝ 1 (periodicWeight (-m) d) := hwt.smooth
  have hwc : Continuous (periodicWeight (-m) d) := hwS.continuous
  have hΦS : ContDiff ℝ 2 Φ := hΦ.smooth
  have hΦc : Continuous Φ := hΦS.continuous
  have hVc : Continuous V := hV.smooth.continuous
  have hV0 : Continuous (fun y => V y 0) := (continuous_apply 0).comp hVc
  have hV1 : Continuous (fun y => V y 1) := (continuous_apply 1).comp hVc
  have hpw0 : Continuous (B0579.pd 0 (periodicWeight (-m) d)) := pd_real_continuous hwS 0
  have hpw1 : Continuous (B0579.pd 1 (periodicWeight (-m) d)) := pd_real_continuous hwS 1
  have hwI : Continuous (wDil m d) := by
    unfold wDil
    exact (continuous_fst.mul hpw0).add (continuous_snd.mul hpw1)
  have hwD : Continuous (wDd m d) := hW.dlenCont
  have hI0 := hΦ.int0
  have hw0 : ∀ y, 0 ≤ periodicWeight (-m) d y := hwt.nonneg
  have hE0nn : 0 ≤ adjE0 d m Φ := by
    unfold adjE0
    exact setIntegral_nonneg hcell (fun y _ => mul_nonneg (hw0 y) (sq_nonneg _))
  have hi : θ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hθ
  have hi0 : 0 ≤ θ⁻¹ := (inv_pos.mpr (by linarith)).le
  -- pointwise bound on the transport-and-weight coefficient
  have hAabs : ∀ y ∈ B0579.cell d,
      |d / (2 * θ) * wDd m d y + 3 * θ⁻¹ * periodicWeight (-m) d y + (2 * θ)⁻¹ * wDil m d y -
        (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
          V y 1 * B0579.pd 1 (periodicWeight (-m) d) y)| ≤
      (2 * K + 3 + 2 * CV * K) * periodicWeight (-m) d y := by
    intro y hy
    exact abs_rate_bound θ d K CV (periodicWeight (-m) d y) (wDd m d y) (wDil m d y)
      (B0579.pd 0 (periodicWeight (-m) d) y) (B0579.pd 1 (periodicWeight (-m) d) y)
      (V y 0) (V y 1) hθ hK hCV (hw0 y) (hW.dlen y hy) (hW.dil y hy)
      (hwt.grad y 0) (hwt.grad y 1) (hV.bound y 0) (hV.bound y 1)
  have hApt : ∀ y ∈ B0579.cell d,
      (d / (2 * θ) * wDd m d y + 3 * θ⁻¹ * periodicWeight (-m) d y + (2 * θ)⁻¹ * wDil m d y -
        (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
          V y 1 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖Φ y‖ ^ 2 ≤
      (2 * K + 3 + 2 * CV * K) * (periodicWeight (-m) d y * ‖Φ y‖ ^ 2) := by
    intro y hy
    have h := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hAabs y hy))
      (sq_nonneg ‖Φ y‖)
    linarith [h]
  have hAc : Continuous (fun y => (d / (2 * θ) * wDd m d y + 3 * θ⁻¹ * periodicWeight (-m) d y +
      (2 * θ)⁻¹ * wDil m d y -
        (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
          V y 1 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖Φ y‖ ^ 2) := by
    have hn : Continuous (fun y => ‖Φ y‖ ^ 2) := (hΦc.norm).pow 2
    exact (((continuous_const.mul hwD).add (continuous_const.mul hwc)).add
      (continuous_const.mul hwI) |>.sub
      ((hV0.mul hpw0).add (hV1.mul hpw1))).mul hn
  have hAint : IntegrableOn (fun y => (d / (2 * θ) * wDd m d y + 3 * θ⁻¹ * periodicWeight (-m) d y +
      (2 * θ)⁻¹ * wDil m d y -
        (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
          V y 1 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖Φ y‖ ^ 2) (B0579.cell d) := by
    refine Integrable.mono' (hI0.const_mul (2 * K + 3 + 2 * CV * K)) hAc.aestronglyMeasurable
      (ae_restrict_of_forall_mem hcell (fun y hy => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖Φ y‖)]
    have h := mul_le_mul_of_nonneg_right (hAabs y hy) (sq_nonneg ‖Φ y‖)
    linarith [h]
  have hP : (∫ y in B0579.cell d, (d / (2 * θ) * wDd m d y + 3 * θ⁻¹ * periodicWeight (-m) d y +
      (2 * θ)⁻¹ * wDil m d y -
        (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
          V y 1 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖Φ y‖ ^ 2) ≤
      (2 * K + 3 + 2 * CV * K) * adjE0 d m Φ := by
    unfold adjE0
    rw [← integral_const_mul]
    exact integral_mono_ae hAint (hI0.const_mul _)
      (ae_restrict_of_forall_mem hcell (fun y hy => hApt y hy))
  -- cross terms
  have hQ : ∀ k : Fin 2, -2 * (∫ y in B0579.cell d,
        B0579.pd k (periodicWeight (-m) d) y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re) ≤
      (∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) +
        K ^ 2 * adjE0 d m Φ :=
    fun k => cross_integral_bound m d K Φ k hK hwt hΦ
  have hQsum : -2 * (∑ k : Fin 2, ∫ y in B0579.cell d,
        B0579.pd k (periodicWeight (-m) d) y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re) ≤
      adjE1 d m Φ + 2 * K ^ 2 * adjE0 d m Φ := by
    unfold adjE1
    simp only [Fin.sum_univ_two]
    linarith [hQ 0, hQ 1]
  have hθQ : -2 * θ⁻¹ * (∑ k : Fin 2, ∫ y in B0579.cell d,
        B0579.pd k (periodicWeight (-m) d) y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re) ≤
      θ⁻¹ * adjE1 d m Φ + 2 * K ^ 2 * adjE0 d m Φ := by
    have h1 := mul_le_mul_of_nonneg_left hQsum hi0
    have h2 : θ⁻¹ * (2 * K ^ 2 * adjE0 d m Φ) ≤ 2 * K ^ 2 * adjE0 d m Φ :=
      mul_le_of_le_one_left (mul_nonneg (by positivity) hE0nn) hi
    linarith [h1, h2]
  -- interaction term
  have hconjχ : AEStronglyMeasurable (fun y => starRingEnd ℂ (Φ y) * χ y)
      (volume.restrict (B0579.cell d)) :=
    (Complex.continuous_conj.comp hΦc).aestronglyMeasurable.mul hχm
  have hRm : AEStronglyMeasurable
      (fun y => periodicWeight (-m) d y * (starRingEnd ℂ (Φ y) * χ y).re)
      (volume.restrict (B0579.cell d)) :=
    hwc.aestronglyMeasurable.mul (Complex.continuous_re.comp_aestronglyMeasurable hconjχ)
  have hGint : Integrable (fun y => -2 * (periodicWeight (-m) d y *
      (starRingEnd ℂ (Φ y) * χ y).re)) (volume.restrict (B0579.cell d)) := by
    refine Integrable.mono' (hI0.add hχint) (hRm.const_mul (-2))
      (ae_restrict_of_forall_mem hcell (fun y _ => ?_))
    rw [Real.norm_eq_abs]
    exact wRe_abs _ _ _ _ (hw0 y) (re_conj_bound (Φ y) (χ y))
  have hR : -2 * (∫ y in B0579.cell d, periodicWeight (-m) d y *
      (starRingEnd ℂ (Φ y) * χ y).re) ≤ (1 + CX) * adjE0 d m Φ := by
    calc -2 * (∫ y in B0579.cell d, periodicWeight (-m) d y * (starRingEnd ℂ (Φ y) * χ y).re)
        = ∫ y in B0579.cell d, -2 * (periodicWeight (-m) d y *
            (starRingEnd ℂ (Φ y) * χ y).re) :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ y in B0579.cell d, (periodicWeight (-m) d y * ‖Φ y‖ ^ 2 +
            periodicWeight (-m) d y * ‖χ y‖ ^ 2) :=
          integral_mono_ae hGint (hI0.fun_add hχint)
            (ae_restrict_of_forall_mem hcell (fun y _ =>
              wRe_pt _ _ _ _ (hw0 y) (re_conj_bound (Φ y) (χ y))))
      _ = adjE0 d m Φ + ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖χ y‖ ^ 2 := by
          rw [integral_add hI0 hχint]
          rfl
      _ ≤ adjE0 d m Φ + CX * adjE0 d m Φ := by linarith [hχb]
      _ = (1 + CX) * adjE0 d m Φ := by ring
  unfold rate0Reduced wRe
  linarith [hP, hθQ, hR, hE0nn]

end UnforcedLeray.Short.IIIa.E0
