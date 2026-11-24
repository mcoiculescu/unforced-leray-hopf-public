import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.DivZero
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_8

/-!
# `PartIII-a:T21/2/2/2/9`: weighted integration by parts of the diffusion on the periodic cell

Source: `the November 2 reference manuscript`, lines 3060-3062 (differentiated
weighted energy; no seam since `w, Φ` are `d`-periodic). Apply `cellDivZero` to
`F_k = w Re(Φ̄ ∂_kΦ)`; `∂_k F_k = ∂_k w Re(Φ̄∂_kΦ) + w‖∂_kΦ‖² + w Re(Φ̄∂_k∂_kΦ)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.Short.IIIa

namespace UnforcedLeray.Short.IIIa.E0

/-- The field `w Re(Φ̄ ∂_kΦ)` of the cell integration by parts. -/
def lapFld (w : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℂ) (k : Fin 2) : ℝ × ℝ → ℝ :=
  fun y => w y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re

theorem re_conj_mul_le (a b : ℂ) : |(starRingEnd ℂ a * b).re| ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h1 : |(starRingEnd ℂ a * b).re| ≤ ‖starRingEnd ℂ a * b‖ := Complex.abs_re_le_norm _
  rw [norm_mul, Complex.norm_conj] at h1
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem pdCx_contDiff_one {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ 2 Φ) (k : Fin 2) :
    ContDiff ℝ 1 (pdCx k Φ) := by
  unfold pdCx
  exact (hΦ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem contDiff_re_conj_mul {Φ g : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ 1 Φ) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun y => (starRingEnd ℂ (Φ y) * g y).re) := by
  have h : ContDiff ℝ 1 (fun y => starRingEnd ℂ (Φ y) * g y) :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hΦ).mul hg
  exact Complex.reCLM.contDiff.comp h

/-- The pointwise derivative of `w Re(Φ̄ ∂_kΦ)` in the direction `k`. -/
theorem pd_lapFld_pt (w : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℂ) (hw : ContDiff ℝ 1 w)
    (hΦ : ContDiff ℝ 2 Φ) (k : Fin 2) (y : ℝ × ℝ) :
    B0579.pd k (lapFld w Φ k) y = B0579.pd k w y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re +
      w y * (‖pdCx k Φ y‖ ^ 2 + (starRingEnd ℂ (Φ y) * pdCx k (pdCx k Φ) y).re) := by
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hgC : ContDiff ℝ 1 (pdCx k Φ) := pdCx_contDiff_one hΦ k
  have hΦd : DifferentiableAt ℝ Φ y := (hΦ1.differentiable (by norm_num)) y
  have hgd : DifferentiableAt ℝ (pdCx k Φ) y := (hgC.differentiable (by norm_num)) y
  have hwd : DifferentiableAt ℝ w y := (hw.differentiable (by norm_num)) y
  have hc : HasFDerivAt (fun x => starRingEnd ℂ (Φ x))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ Φ y)) y := by
    have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp y hΦd.hasFDerivAt
    simpa [Function.comp_def] using h
  have hQ : HasFDerivAt (fun x => starRingEnd ℂ (Φ x) * pdCx k Φ x)
      ((starRingEnd ℂ (Φ y)) • fderiv ℝ (pdCx k Φ) y +
        (pdCx k Φ y) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ Φ y))) y :=
    hc.mul hgd.hasFDerivAt
  have hR : HasFDerivAt (fun x => (starRingEnd ℂ (Φ x) * pdCx k Φ x).re)
      (Complex.reCLM.comp ((starRingEnd ℂ (Φ y)) • fderiv ℝ (pdCx k Φ) y +
        (pdCx k Φ y) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ Φ y)))) y :=
    Complex.reCLM.hasFDerivAt.comp y hQ
  have hF : HasFDerivAt (lapFld w Φ k)
      (w y • Complex.reCLM.comp ((starRingEnd ℂ (Φ y)) • fderiv ℝ (pdCx k Φ) y +
        (pdCx k Φ y) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ Φ y))) +
        (starRingEnd ℂ (Φ y) * pdCx k Φ y).re • fderiv ℝ w y) y :=
    hwd.hasFDerivAt.mul hR
  have hgg : (pdCx k Φ y * starRingEnd ℂ (pdCx k Φ y)).re = ‖pdCx k Φ y‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hcj : ∀ z : ℂ, (Complex.conjCLE : ℂ →L[ℝ] ℂ) z = starRingEnd ℂ z := fun z => rfl
  have e1 : (fderiv ℝ (pdCx k Φ) y) (B0579.dir k) = pdCx k (pdCx k Φ) y := rfl
  have e2 : (fderiv ℝ Φ y) (B0579.dir k) = pdCx k Φ y := rfl
  unfold B0579.pd
  rw [hF.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.reCLM_apply, hcj,
    smul_eq_mul, Complex.add_re]
  rw [e1, e2, hgg]
  ring

/-- **Weighted integration by parts of the diffusion on the periodic cell** (SP 3060-3062). -/
theorem cellLapIBP : UnforcedLeray.Short.IIIa.E0.CellLapIBP := by
  intro d K w Φ hd hw hΦ hper hi0 hi1 hiL
  have hw1 : ContDiff ℝ 1 w := hw.smooth
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hΦc : Continuous Φ := hΦ.continuous
  have hpd1 : ∀ k, ContDiff ℝ 1 (pdCx k Φ) := fun k => pdCx_contDiff_one hΦ k
  have hpdc : ∀ k, Continuous (pdCx k Φ) := fun k => (hpd1 k).continuous
  have hwc : Continuous w := hw1.continuous
  have hpdw : ∀ k, Continuous (B0579.pd k w) := fun k => by
    unfold B0579.pd
    exact (hw1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hRc : ∀ k, Continuous (fun y => (starRingEnd ℂ (Φ y) * pdCx k Φ y).re) := fun k =>
    Complex.continuous_re.comp ((Complex.continuous_conj.comp hΦc).mul (hpdc k))
  have hLc : ∀ k, Continuous (lapFld w Φ k) := fun k => hwc.mul (hRc k)
  have hFbound : ∀ k, ∀ y, ‖lapFld w Φ k y‖ ≤ w y * ‖Φ y‖ ^ 2 + w y * ‖pdCx k Φ y‖ ^ 2 := by
    intro k y
    show ‖w y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw.nonneg y)]
    have := mul_le_mul_of_nonneg_left (re_conj_mul_le (Φ y) (pdCx k Φ y)) (hw.nonneg y)
    linarith [mul_add (w y) (‖Φ y‖ ^ 2) (‖pdCx k Φ y‖ ^ 2)]
  have hi_F : ∀ k, IntegrableOn (lapFld w Φ k) (B0579.cell d) := fun k =>
    Integrable.mono' (hi0.add (hi1 k)) (hLc k).aestronglyMeasurable
      (ae_of_all _ fun y => hFbound k y)
  have hA : ∀ k, IntegrableOn (fun y => B0579.pd k w y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re)
      (B0579.cell d) := by
    intro k
    refine Integrable.mono' ((hi0.add (hi1 k)).const_mul |K|)
      ((hpdw k).mul (hRc k)).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    show ‖B0579.pd k w y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re‖ ≤
      |K| * (w y * ‖Φ y‖ ^ 2 + w y * ‖pdCx k Φ y‖ ^ 2)
    have h1 : |B0579.pd k w y| ≤ |K| * w y :=
      le_trans (hw.grad y k) (mul_le_mul_of_nonneg_right (le_abs_self K) (hw.nonneg y))
    have h2 := re_conj_mul_le (Φ y) (pdCx k Φ y)
    rw [Real.norm_eq_abs, abs_mul]
    calc |B0579.pd k w y| * |(starRingEnd ℂ (Φ y) * pdCx k Φ y).re|
        ≤ (|K| * w y) * (‖Φ y‖ ^ 2 + ‖pdCx k Φ y‖ ^ 2) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (abs_nonneg _) (hw.nonneg y))
      _ = |K| * (w y * ‖Φ y‖ ^ 2 + w y * ‖pdCx k Φ y‖ ^ 2) := by ring
  have hpt : ∀ y, B0579.pd 0 (lapFld w Φ 0) y + B0579.pd 1 (lapFld w Φ 1) y =
      ((B0579.pd 0 w y * (starRingEnd ℂ (Φ y) * pdCx 0 Φ y).re +
          B0579.pd 1 w y * (starRingEnd ℂ (Φ y) * pdCx 1 Φ y).re) +
        (w y * ‖pdCx 0 Φ y‖ ^ 2 + w y * ‖pdCx 1 Φ y‖ ^ 2)) +
        w y * (starRingEnd ℂ (Φ y) * lapCx Φ y).re := by
    intro y
    rw [pd_lapFld_pt w Φ hw1 hΦ 0 y, pd_lapFld_pt w Φ hw1 hΦ 1 y]
    unfold lapCx
    simp only [mul_add, Complex.add_re]
    ring
  have hA01 : IntegrableOn (fun y => B0579.pd 0 w y * (starRingEnd ℂ (Φ y) * pdCx 0 Φ y).re +
      B0579.pd 1 w y * (starRingEnd ℂ (Φ y) * pdCx 1 Φ y).re) (B0579.cell d) :=
    (hA 0).add (hA 1)
  have hB : IntegrableOn (fun y => w y * ‖pdCx 0 Φ y‖ ^ 2 + w y * ‖pdCx 1 Φ y‖ ^ 2)
      (B0579.cell d) := (hi1 0).add (hi1 1)
  have hpdsum : IntegrableOn (fun y => B0579.pd 0 (lapFld w Φ 0) y +
      B0579.pd 1 (lapFld w Φ 1) y) (B0579.cell d) :=
    ((hA01.add hB).add hiL).congr (ae_of_all _ fun y => (hpt y).symm)
  have hperF : ∀ k : Fin 2, ∀ y : ℝ × ℝ, lapFld w Φ k (y.1 + d, y.2) = lapFld w Φ k y := by
    intro k y
    show w (y.1 + d, y.2) * (starRingEnd ℂ (Φ (y.1 + d, y.2)) * pdCx k Φ (y.1 + d, y.2)).re =
      w y * (starRingEnd ℂ (Φ y) * pdCx k Φ y).re
    rw [hw.periodic y, hper y, UnforcedLeray.Short.IIIa.AdjE1.pdCx_periodic d hper k y]
  have hF0 : ContDiff ℝ 1 (lapFld w Φ 0) :=
    hw1.mul (contDiff_re_conj_mul hΦ1 (hpd1 0))
  have hF1 : ContDiff ℝ 1 (lapFld w Φ 1) :=
    hw1.mul (contDiff_re_conj_mul hΦ1 (hpd1 1))
  have hzero := cellDivZero d hd (lapFld w Φ 0) (lapFld w Φ 1) hF0 hF1 (hperF 0) (hi_F 1) hpdsum
  have e : ∫ y in B0579.cell d, (B0579.pd 0 (lapFld w Φ 0) y + B0579.pd 1 (lapFld w Φ 1) y) =
      ∫ y in B0579.cell d, (((B0579.pd 0 w y * (starRingEnd ℂ (Φ y) * pdCx 0 Φ y).re +
          B0579.pd 1 w y * (starRingEnd ℂ (Φ y) * pdCx 1 Φ y).re) +
        (w y * ‖pdCx 0 Φ y‖ ^ 2 + w y * ‖pdCx 1 Φ y‖ ^ 2)) +
        w y * (starRingEnd ℂ (Φ y) * lapCx Φ y).re) :=
    integral_congr_ae (ae_of_all _ fun y => hpt y)
  have s1 := integral_add (hA01.add hB) hiL
  have s2 := integral_add hA01 hB
  have s3 := integral_add (hA 0) (hA 1)
  have s4 := integral_add (hi1 0) (hi1 1)
  try simp only [Pi.add_apply] at s1 s2
  try beta_reduce at s1 s2 s3 s4
  simp only [Fin.sum_univ_two]
  linarith [hzero, e, s1, s2, s3, s4]

end UnforcedLeray.Short.IIIa.E0
