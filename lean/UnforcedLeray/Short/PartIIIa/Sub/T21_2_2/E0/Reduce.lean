import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.LapIBP
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.TransIBP

/-!
# `PartIII-a:T21/2/2/2/11`: the cell rate reduction (SP 3060-3062)

Source: `the November 2 reference manuscript`, lines 3060-3062. Unfolding
`rate0` and `rate0Reduced`, the pointwise identity `wRe Φ Ψ = θ⁻¹ w Re(Φ̄ΔΦ) + θ⁻¹ w|Φ|² +
w Re(Φ̄ V·∇Φ) - w Re(Φ̄χ)` for `Ψ = adjPsi`, the weighted integration by parts `cellLapIBP`
(diffusion, `/9`) and `cellTransportIBP` (transport, `/10`), and the integrability of each piece
(weight bounds `WeightHyp`, `CellDrift`, the interaction hypothesis) give the identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.Short.IIIa

namespace UnforcedLeray.Short.IIIa.E0

/-- `Re(z̄ z) = |z|²`. -/
theorem re_conj_self_eq (z : ℂ) : (starRingEnd ℂ z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]
  ring

/-- Pointwise splitting of `w Re(Φ̄ Ψ)` for `Ψ = adjPsi θ Φ χ V`. -/
theorem wRe_adjPsi (m d θ : ℝ) (Φ χ : ℝ × ℝ → ℂ) (V : ℝ × ℝ → Fin 2 → ℝ) (y : ℝ × ℝ) :
    wRe m d Φ (adjPsi θ Φ χ V) y =
      θ⁻¹ * (periodicWeight (-m) d y * (starRingEnd ℂ (Φ y) * lapCx Φ y).re) +
      θ⁻¹ * (periodicWeight (-m) d y * ‖Φ y‖ ^ 2) +
      periodicWeight (-m) d y * (starRingEnd ℂ (Φ y) * transCx V Φ y).re -
      wRe m d Φ χ y := by
  have hc : starRingEnd ℂ (Φ y) * adjPsi θ Φ χ V y =
      ((θ⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ (Φ y) * lapCx Φ y) +
      ((θ⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ (Φ y) * Φ y) +
      starRingEnd ℂ (Φ y) * transCx V Φ y - starRingEnd ℂ (Φ y) * χ y := by
    unfold adjPsi; ring
  unfold wRe
  rw [hc]
  simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, re_conj_self_eq]
  ring

/-- Integrability on the cell from a pointwise bound by an integrable majorant. -/
theorem intOn_of_bd {C : Set (ℝ × ℝ)} (hC : MeasurableSet C) {f g : ℝ × ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict C)) (hg : IntegrableOn g C)
    (h : ∀ y ∈ C, ‖f y‖ ≤ g y) : IntegrableOn f C :=
  Integrable.mono' hg hf (by
    filter_upwards [ae_restrict_mem hC] with y hy
    exact h y hy)

/-- **The rate after the integrations by parts** (SP 3060-3062). -/
theorem cellRateReduce : UnforcedLeray.Short.IIIa.E0.CellRateReduce := by
  intro m K CV d θ Φ χ V hd hθ hW hΦ hV hχm hχi hΨ
  have hcell : B0579.cell d = UnforcedLeray.Cyl.cell d := by
    unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hC : MeasurableSet (B0579.cell d) := by
    rw [hcell]; exact UnforcedLeray.Cyl.measurableSet_cell d
  have hwb := hW.base
  have hw1 : ContDiff ℝ 1 (periodicWeight (-m) d) := hwb.smooth
  have hwc : Continuous (periodicWeight (-m) d) := hw1.continuous
  have hwn : ∀ y, 0 ≤ periodicWeight (-m) d y := hwb.nonneg
  have hpdw : ∀ k : Fin 2, Continuous (B0579.pd k (periodicWeight (-m) d)) := fun k => by
    unfold B0579.pd
    exact (hw1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hΦc : Continuous Φ := hΦ.smooth.continuous
  have hNc : Continuous (fun y => ‖Φ y‖ ^ 2) := hΦc.norm.pow 2
  have hpdΦ : ∀ k : Fin 2, Continuous (pdCx k Φ) := fun k =>
    (pdCx_contDiff_one hΦ.smooth k).continuous
  have hVc : Continuous V := hV.smooth.continuous
  have hVk : ∀ k : Fin 2, Continuous (fun y => V y k) := fun k =>
    (continuous_apply k).comp hVc
  have hCV : 0 ≤ CV := le_trans (abs_nonneg _) (hV.bound 0 0)
  have hNint : IntegrableOn (fun y => periodicWeight (-m) d y * ‖Φ y‖ ^ 2) (B0579.cell d) :=
    hΦ.int0
  have hN1 : ∀ k : Fin 2, IntegrableOn (fun y => periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2)
      (B0579.cell d) := hΦ.int1
  have hdl : Continuous (wDd m d) := hW.dlenCont
  have hwDilc : Continuous (wDil m d) := by
    have : Continuous (fun y : ℝ × ℝ => y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
        y.2 * B0579.pd 1 (periodicWeight (-m) d) y) :=
      (continuous_fst.mul (hpdw 0)).add (continuous_snd.mul (hpdw 1))
    exact this
  -- the interaction term `w Re(Φ̄ χ)`
  have hXint : IntegrableOn (fun y => wRe m d Φ χ y) (B0579.cell d) := by
    refine intOn_of_bd hC ?_ (hNint.fun_add hχi) ?_
    · exact hwc.aestronglyMeasurable.mul
        (Complex.continuous_re.comp_aestronglyMeasurable
          ((Complex.continuous_conj.comp hΦc).aestronglyMeasurable.mul hχm))
    · intro y _
      try dsimp only
      unfold wRe
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwn y)]
      have h := mul_le_mul_of_nonneg_left (re_conj_mul_le (Φ y) (χ y)) (hwn y)
      rw [mul_add] at h
      exact h
  -- the transport term `w Re(Φ̄ V·∇Φ)`
  have hTint : IntegrableOn (fun y => periodicWeight (-m) d y *
      (starRingEnd ℂ (Φ y) * transCx V Φ y).re) (B0579.cell d) := by
    have hTc : Continuous (fun y => transCx V Φ y) := by
      unfold transCx
      exact ((Complex.continuous_ofReal.comp (hVk 0)).mul (hpdΦ 0)).add
        ((Complex.continuous_ofReal.comp (hVk 1)).mul (hpdΦ 1))
    have hcont : Continuous (fun y => periodicWeight (-m) d y *
        (starRingEnd ℂ (Φ y) * transCx V Φ y).re) :=
      hwc.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp hΦc).mul hTc))
    refine intOn_of_bd hC hcont.aestronglyMeasurable
      (((hNint.const_mul CV).fun_add ((hN1 0).const_mul CV)).fun_add ((hN1 1).const_mul CV)) ?_
    intro y _
    try dsimp only
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwn y)]
    have h1 := re_conj_mul_norm_le (Φ y) (transCx V Φ y)
    have h2 := norm_transCx_le V Φ CV hCV y (hV.bound y 0) (hV.bound y 1)
    have h3 : periodicWeight (-m) d y * |(starRingEnd ℂ (Φ y) * transCx V Φ y).re| ≤
        periodicWeight (-m) d y * (‖Φ y‖ * (CV * ‖pdCx 0 Φ y‖ + CV * ‖pdCx 1 Φ y‖)) :=
      mul_le_mul_of_nonneg_left (le_trans h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
        (hwn y)
    have h4 : ‖Φ y‖ * (CV * ‖pdCx 0 Φ y‖ + CV * ‖pdCx 1 Φ y‖) ≤
        CV * (‖Φ y‖ ^ 2 + ‖pdCx 0 Φ y‖ ^ 2 + ‖pdCx 1 Φ y‖ ^ 2) := by
      nlinarith [mul_nonneg hCV (sq_nonneg (‖Φ y‖ - ‖pdCx 0 Φ y‖)),
        mul_nonneg hCV (sq_nonneg (‖Φ y‖ - ‖pdCx 1 Φ y‖)),
        mul_nonneg hCV (sq_nonneg (‖pdCx 0 Φ y‖)), mul_nonneg hCV (sq_nonneg (‖pdCx 1 Φ y‖))]
    calc periodicWeight (-m) d y * |(starRingEnd ℂ (Φ y) * transCx V Φ y).re|
        ≤ periodicWeight (-m) d y * (‖Φ y‖ * (CV * ‖pdCx 0 Φ y‖ + CV * ‖pdCx 1 Φ y‖)) := h3
      _ ≤ periodicWeight (-m) d y * (CV * (‖Φ y‖ ^ 2 + ‖pdCx 0 Φ y‖ ^ 2 + ‖pdCx 1 Φ y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h4 (hwn y)
      _ = CV * (periodicWeight (-m) d y * ‖Φ y‖ ^ 2) +
            CV * (periodicWeight (-m) d y * ‖pdCx 0 Φ y‖ ^ 2) +
            CV * (periodicWeight (-m) d y * ‖pdCx 1 Φ y‖ ^ 2) := by ring
  -- the adjoint localized term `A = w Re(Φ̄ ΔΦ)`, recovered from `Ψ`
  have hAint : IntegrableOn (fun y => periodicWeight (-m) d y *
      (starRingEnd ℂ (Φ y) * lapCx Φ y).re) (B0579.cell d) := by
    have h : IntegrableOn (fun y => θ * wRe m d Φ (adjPsi θ Φ χ V) y -
        periodicWeight (-m) d y * ‖Φ y‖ ^ 2 - θ * (periodicWeight (-m) d y *
          (starRingEnd ℂ (Φ y) * transCx V Φ y).re) +
        θ * wRe m d Φ χ y) (B0579.cell d) :=
      ((((hΨ.const_mul θ).sub hNint).sub (hTint.const_mul θ)).add (hXint.const_mul θ))
    refine h.congr_fun (fun y _ => ?_) hC
    try dsimp only
    have hwy := wRe_adjPsi m d θ Φ χ V y
    have hθ' : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ.ne'
    linear_combination θ * hwy +
      (periodicWeight (-m) d y * (starRingEnd ℂ (Φ y) * lapCx Φ y).re +
        periodicWeight (-m) d y * ‖Φ y‖ ^ 2) * hθ'
  -- the moving transport weight `V·∇w |Φ|²`
  have hVint : IntegrableOn (fun y => (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
      V y 1 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖Φ y‖ ^ 2) (B0579.cell d) := by
    have hcont : Continuous (fun y => (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
        V y 1 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖Φ y‖ ^ 2) :=
      ((((hVk 0).mul (hpdw 0)).add ((hVk 1).mul (hpdw 1))).mul hNc)
    refine intOn_of_bd hC hcont.aestronglyMeasurable (hNint.const_mul (2 * CV * K)) ?_
    intro y _
    try dsimp only
    have e0 : |V y 0 * B0579.pd 0 (periodicWeight (-m) d) y| ≤
        CV * (K * periodicWeight (-m) d y) := by
      rw [abs_mul]
      exact mul_le_mul (hV.bound y 0) (hwb.grad y 0) (abs_nonneg _) hCV
    have e1 : |V y 1 * B0579.pd 1 (periodicWeight (-m) d) y| ≤
        CV * (K * periodicWeight (-m) d y) := by
      rw [abs_mul]
      exact mul_le_mul (hV.bound y 1) (hwb.grad y 1) (abs_nonneg _) hCV
    have hs : |V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
        V y 1 * B0579.pd 1 (periodicWeight (-m) d) y| ≤
        CV * (K * periodicWeight (-m) d y) + CV * (K * periodicWeight (-m) d y) := by
      linarith [abs_add_le (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y)
        (V y 1 * B0579.pd 1 (periodicWeight (-m) d) y)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖Φ y‖)]
    calc |V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
          V y 1 * B0579.pd 1 (periodicWeight (-m) d) y| * ‖Φ y‖ ^ 2
        ≤ (CV * (K * periodicWeight (-m) d y) + CV * (K * periodicWeight (-m) d y)) *
            ‖Φ y‖ ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = 2 * CV * K * (periodicWeight (-m) d y * ‖Φ y‖ ^ 2) := by ring
  -- the cell-level rate integrand `(d/(2θ))wDd + θ⁻¹ w + (2θ)⁻¹ wDil`
  have hP1 : IntegrableOn (fun y => (d / (2 * θ) * wDd m d y + θ⁻¹ * periodicWeight (-m) d y +
      (2 * θ)⁻¹ * wDil m d y) * ‖Φ y‖ ^ 2) (B0579.cell d) := by
    have hb : 0 < (2 * θ)⁻¹ := by positivity
    have hcont : Continuous (fun y => (d / (2 * θ) * wDd m d y +
        θ⁻¹ * periodicWeight (-m) d y + (2 * θ)⁻¹ * wDil m d y) * ‖Φ y‖ ^ 2) :=
      ((((continuous_const.mul hdl).add (continuous_const.mul hwc)).add
        (continuous_const.mul hwDilc)).mul hNc)
    refine intOn_of_bd hC hcont.aestronglyMeasurable
      (hNint.const_mul ((2 * θ)⁻¹ * K + θ⁻¹ + (2 * θ)⁻¹ * K)) ?_
    intro y hy
    try dsimp only
    have h1 : |d / (2 * θ) * wDd m d y| ≤ (2 * θ)⁻¹ * (K * periodicWeight (-m) d y) := by
      have e : d / (2 * θ) * wDd m d y = (2 * θ)⁻¹ * (d * wDd m d y) := by ring
      rw [e, abs_mul, abs_of_pos hb]
      exact mul_le_mul_of_nonneg_left (hW.dlen y hy) hb.le
    have h2 : |θ⁻¹ * periodicWeight (-m) d y| = θ⁻¹ * periodicWeight (-m) d y := by
      rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 hθ.le) (hwn y))]
    have h3 : |(2 * θ)⁻¹ * wDil m d y| ≤ (2 * θ)⁻¹ * (K * periodicWeight (-m) d y) := by
      rw [abs_mul, abs_of_pos hb]
      exact mul_le_mul_of_nonneg_left (hW.dil y hy) hb.le
    have hs : |d / (2 * θ) * wDd m d y + θ⁻¹ * periodicWeight (-m) d y +
        (2 * θ)⁻¹ * wDil m d y| ≤ (2 * θ)⁻¹ * (K * periodicWeight (-m) d y) +
          θ⁻¹ * periodicWeight (-m) d y + (2 * θ)⁻¹ * (K * periodicWeight (-m) d y) := by
      linarith [abs_add_le (d / (2 * θ) * wDd m d y + θ⁻¹ * periodicWeight (-m) d y)
          ((2 * θ)⁻¹ * wDil m d y),
        abs_add_le (d / (2 * θ) * wDd m d y) (θ⁻¹ * periodicWeight (-m) d y)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖Φ y‖)]
    calc |d / (2 * θ) * wDd m d y + θ⁻¹ * periodicWeight (-m) d y +
          (2 * θ)⁻¹ * wDil m d y| * ‖Φ y‖ ^ 2
        ≤ ((2 * θ)⁻¹ * (K * periodicWeight (-m) d y) + θ⁻¹ * periodicWeight (-m) d y +
            (2 * θ)⁻¹ * (K * periodicWeight (-m) d y)) * ‖Φ y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = ((2 * θ)⁻¹ * K + θ⁻¹ + (2 * θ)⁻¹ * K) *
            (periodicWeight (-m) d y * ‖Φ y‖ ^ 2) := by ring
  -- the diffusion integration by parts and the transport integration by parts
  have hL : ∫ y in B0579.cell d, periodicWeight (-m) d y * (starRingEnd ℂ (Φ y) * lapCx Φ y).re =
      -(adjE1 d m Φ) - ∑ k : Fin 2, ∫ y in B0579.cell d,
        B0579.pd k (periodicWeight (-m) d) y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re := by
    have h := cellLapIBP d K (periodicWeight (-m) d) Φ hd hwb hΦ.smooth hΦ.periodic
      hΦ.int0 hΦ.int1 hAint
    unfold adjE1
    exact h
  have hT : ∫ y in B0579.cell d, periodicWeight (-m) d y *
      (starRingEnd ℂ (Φ y) * transCx V Φ y).re =
      -(1 / 2) * ∫ y in B0579.cell d, (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
        V y 1 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖Φ y‖ ^ 2 :=
    cellTransportIBP d K CV (periodicWeight (-m) d) Φ V hd hwb (hΦ.smooth.of_le (by norm_num))
      hΦ.periodic hΦ.int0 hΦ.int1 hV
  -- the splitting of the energy rate
  have hJ : ∫ y in B0579.cell d, wRe m d Φ (adjPsi θ Φ χ V) y =
      θ⁻¹ * (∫ y in B0579.cell d, periodicWeight (-m) d y *
        (starRingEnd ℂ (Φ y) * lapCx Φ y).re) +
      θ⁻¹ * (∫ y in B0579.cell d, periodicWeight (-m) d y * ‖Φ y‖ ^ 2) +
      (∫ y in B0579.cell d, periodicWeight (-m) d y *
        (starRingEnd ℂ (Φ y) * transCx V Φ y).re) -
      ∫ y in B0579.cell d, wRe m d Φ χ y := by
    have hpt : (∫ y in B0579.cell d, wRe m d Φ (adjPsi θ Φ χ V) y) =
        ∫ y in B0579.cell d, (θ⁻¹ * (periodicWeight (-m) d y *
            (starRingEnd ℂ (Φ y) * lapCx Φ y).re) +
          θ⁻¹ * (periodicWeight (-m) d y * ‖Φ y‖ ^ 2) +
          periodicWeight (-m) d y * (starRingEnd ℂ (Φ y) * transCx V Φ y).re -
          wRe m d Φ χ y) := by
      congr 1
      funext y
      exact wRe_adjPsi m d θ Φ χ V y
    have hA1 := hAint.const_mul θ⁻¹
    have hN1' := hNint.const_mul θ⁻¹
    have i0 : IntegrableOn (fun y => θ⁻¹ * (periodicWeight (-m) d y *
        (starRingEnd ℂ (Φ y) * lapCx Φ y).re) + θ⁻¹ * (periodicWeight (-m) d y *
        ‖Φ y‖ ^ 2)) (B0579.cell d) := hA1.fun_add hN1'
    have i1 : IntegrableOn (fun y => θ⁻¹ * (periodicWeight (-m) d y *
        (starRingEnd ℂ (Φ y) * lapCx Φ y).re) + θ⁻¹ * (periodicWeight (-m) d y *
        ‖Φ y‖ ^ 2) + periodicWeight (-m) d y *
        (starRingEnd ℂ (Φ y) * transCx V Φ y).re) (B0579.cell d) := i0.fun_add hTint
    rw [hpt, integral_sub i1 hXint, integral_add i0 hTint, integral_add hA1 hN1',
      integral_const_mul, integral_const_mul]
  have hP2 : ∫ y in B0579.cell d, (d / (2 * θ) * wDd m d y + 3 * θ⁻¹ * periodicWeight (-m) d y +
      (2 * θ)⁻¹ * wDil m d y - (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
        V y 1 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖Φ y‖ ^ 2 =
      (∫ y in B0579.cell d, (d / (2 * θ) * wDd m d y + θ⁻¹ * periodicWeight (-m) d y +
        (2 * θ)⁻¹ * wDil m d y) * ‖Φ y‖ ^ 2) +
      2 * θ⁻¹ * (∫ y in B0579.cell d, periodicWeight (-m) d y * ‖Φ y‖ ^ 2) -
      ∫ y in B0579.cell d, (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
        V y 1 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖Φ y‖ ^ 2 := by
    have hpt : (∫ y in B0579.cell d, (d / (2 * θ) * wDd m d y + 3 * θ⁻¹ *
        periodicWeight (-m) d y + (2 * θ)⁻¹ * wDil m d y - (V y 0 *
          B0579.pd 0 (periodicWeight (-m) d) y + V y 1 *
          B0579.pd 1 (periodicWeight (-m) d) y)) * ‖Φ y‖ ^ 2) =
        ∫ y in B0579.cell d, (((d / (2 * θ) * wDd m d y + θ⁻¹ * periodicWeight (-m) d y +
          (2 * θ)⁻¹ * wDil m d y) * ‖Φ y‖ ^ 2) +
          2 * θ⁻¹ * (periodicWeight (-m) d y * ‖Φ y‖ ^ 2)) -
          (V y 0 * B0579.pd 0 (periodicWeight (-m) d) y +
            V y 1 * B0579.pd 1 (periodicWeight (-m) d) y) * ‖Φ y‖ ^ 2 := by
      congr 1
      funext y
      ring
    have hN2 := hNint.const_mul (2 * θ⁻¹)
    have i2 : IntegrableOn (fun y => (d / (2 * θ) * wDd m d y + θ⁻¹ * periodicWeight (-m) d y +
        (2 * θ)⁻¹ * wDil m d y) * ‖Φ y‖ ^ 2 + 2 * θ⁻¹ * (periodicWeight (-m) d y *
        ‖Φ y‖ ^ 2)) (B0579.cell d) := hP1.fun_add hN2
    rw [hpt, integral_sub i2 hVint, integral_add hP1 hN2, integral_const_mul]
  unfold rate0 rate0Reduced
  rw [hP2, hJ, hL, hT]
  ring

end UnforcedLeray.Short.IIIa.E0
