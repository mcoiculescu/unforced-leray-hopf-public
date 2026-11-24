import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.DivZero
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_8

/-!
# `PartIII-a:T21/2/2/2/10`: weighted integration by parts of the transport on the periodic cell

Source: `the November 2 reference manuscript`, lines 2954-2955. Apply `cellDivZero`
to `F_k = V_k w |Φ|²`. The divergence is `(V·∇w)|Φ|² + 2 w Re(Φ̄ V·∇Φ) + (div V) w |Φ|²`, and
`div V = 0` removes the last term.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.Short.IIIa
open UnforcedLeray.Short.IIIa.AdjE1 (pd_mul pd_normSq)

namespace UnforcedLeray.Short.IIIa.E0

theorem re_conj_transCx (V : ℝ × ℝ → Fin 2 → ℝ) (Φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    (starRingEnd ℂ (Φ y) * transCx V Φ y).re =
      V y 0 * (starRingEnd ℂ (Φ y) * pdCx 0 Φ y).re +
        V y 1 * (starRingEnd ℂ (Φ y) * pdCx 1 Φ y).re := by
  have key : ∀ (a : ℝ) (z u : ℂ), (z * ((a : ℂ) * u)).re = a * (z * u).re := by
    intro a z u
    have h : z * ((a : ℂ) * u) = (a : ℂ) * (z * u) := by ring
    rw [h, Complex.re_ofReal_mul]
  unfold transCx
  rw [mul_add, Complex.add_re, key, key]

theorem re_conj_mul_norm_le (a b : ℂ) : |(starRingEnd ℂ a * b).re| ≤ ‖a‖ * ‖b‖ := by
  have h1 : |(starRingEnd ℂ a * b).re| ≤ ‖starRingEnd ℂ a * b‖ := Complex.abs_re_le_norm _
  rw [norm_mul, Complex.norm_conj] at h1
  exact h1

theorem norm_transCx_le (V : ℝ × ℝ → Fin 2 → ℝ) (Φ : ℝ × ℝ → ℂ) (CV : ℝ) (hCV : 0 ≤ CV)
    (y : ℝ × ℝ) (h0 : |V y 0| ≤ CV) (h1 : |V y 1| ≤ CV) :
    ‖transCx V Φ y‖ ≤ CV * ‖pdCx 0 Φ y‖ + CV * ‖pdCx 1 Φ y‖ := by
  unfold transCx
  calc ‖(V y 0 : ℂ) * pdCx 0 Φ y + (V y 1 : ℂ) * pdCx 1 Φ y‖
      ≤ ‖(V y 0 : ℂ) * pdCx 0 Φ y‖ + ‖(V y 1 : ℂ) * pdCx 1 Φ y‖ := norm_add_le _ _
    _ = |V y 0| * ‖pdCx 0 Φ y‖ + |V y 1| * ‖pdCx 1 Φ y‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ CV * ‖pdCx 0 Φ y‖ + CV * ‖pdCx 1 Φ y‖ :=
        add_le_add (mul_le_mul_of_nonneg_right h0 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))

/-- **Weighted integration by parts of the transport on the periodic cell** (SP 2954-2955). -/
theorem cellTransportIBP : UnforcedLeray.Short.IIIa.E0.CellTransportIBP := by
  intro d K CV w Φ V hd hw hΦ hper hi0 hi1 hV
  have hw1 : ContDiff ℝ 1 w := hw.smooth
  have hΦc : Continuous Φ := hΦ.continuous
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hV1 : ContDiff ℝ 1 V := hV.smooth
  have hVc : Continuous V := hV1.continuous
  have hVk1 : ∀ k : Fin 2, ContDiff ℝ 1 (fun x => V x k) := fun k =>
    (ContinuousLinearMap.proj k : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff.comp hV1
  have hV0 := hVk1 0
  have hV1' := hVk1 1
  have hN : ContDiff ℝ 1 (fun x => ‖Φ x‖ ^ 2) := ContDiff.norm_sq (𝕜 := ℝ) hΦ
  have hwc : Continuous w := hw1.continuous
  have hNc : Continuous (fun x => ‖Φ x‖ ^ 2) := hN.continuous
  have hCV : 0 ≤ CV := le_trans (abs_nonneg _) (hV.bound 0 0)
  have hNc : Continuous (fun x => ‖Φ x‖ ^ 2) := hN.continuous
  have hpdw : ∀ k, Continuous (B0579.pd k w) := fun k => by
    unfold B0579.pd
    exact (hw1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- the integrability of the basic weights
  -- the flux fields
  have hF : ∀ k : Fin 2, ContDiff ℝ 1 (fun x => V x k * (w x * ‖Φ x‖ ^ 2)) := by
    intro k
    exact (hVk1 k).mul (hw1.mul hN)
  have hFc : ∀ k : Fin 2, Continuous (fun x => V x k * (w x * ‖Φ x‖ ^ 2)) := fun k =>
    (hF k).continuous
  have hFint : ∀ k : Fin 2, IntegrableOn (fun x => V x k * (w x * ‖Φ x‖ ^ 2)) (B0579.cell d) := by
    intro k
    refine Integrable.mono' (hi0.const_mul CV) (hFc k).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    show ‖V y k * (w y * ‖Φ y‖ ^ 2)‖ ≤ CV * (w y * ‖Φ y‖ ^ 2)
    have hwN : 0 ≤ w y * ‖Φ y‖ ^ 2 := mul_nonneg (hw.nonneg y) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwN]
    exact mul_le_mul_of_nonneg_right (hV.bound y k) hwN
  -- pointwise divergence identity
  have hpt : ∀ y : ℝ × ℝ,
      B0579.pd 0 (fun x => V x 0 * (w x * ‖Φ x‖ ^ 2)) y +
        B0579.pd 1 (fun x => V x 1 * (w x * ‖Φ x‖ ^ 2)) y =
      (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y) * ‖Φ y‖ ^ 2 +
        2 * (w y * (starRingEnd ℂ (Φ y) * transCx V Φ y).re) := by
    intro y
    have hV0d : DifferentiableAt ℝ (fun x => V x 0) y := (hV0.differentiable (by norm_num)) y
    have hV1d : DifferentiableAt ℝ (fun x => V x 1) y := (hV1'.differentiable (by norm_num)) y
    have hwd : DifferentiableAt ℝ w y := (hw1.differentiable (by norm_num)) y
    have hNd : DifferentiableAt ℝ (fun x => ‖Φ x‖ ^ 2) y := (hN.differentiable (by norm_num)) y
    have hwNd : DifferentiableAt ℝ (fun x => w x * ‖Φ x‖ ^ 2) y := hwd.mul hNd
    rw [pd_mul hV0d hwNd 0, pd_mul hV1d hwNd 1]
    rw [pd_mul hwd hNd 0, pd_mul hwd hNd 1]
    rw [pd_normSq hΦd 0 y, pd_normSq hΦd 1 y, re_conj_transCx]
    have hdiv := hV.divFree y
    linear_combination (w y * ‖Φ y‖ ^ 2) * hdiv
  have hpdΦ : ∀ k : Fin 2, Continuous (pdCx k Φ) := fun k => by
    unfold pdCx
    exact (hΦ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hVk : ∀ k : Fin 2, Continuous (fun y => V y k) := fun k => (continuous_apply k).comp hVc
  have hTc : Continuous (fun y => transCx V Φ y) := by
    unfold transCx
    exact (((Complex.continuous_ofReal.comp (hVk 0)).mul (hpdΦ 0)).add
      ((Complex.continuous_ofReal.comp (hVk 1)).mul (hpdΦ 1)))
  have hW : IntegrableOn (fun y => w y * (starRingEnd ℂ (Φ y) * transCx V Φ y).re)
      (B0579.cell d) := by
    refine Integrable.mono' (((hi0.const_mul CV).add ((hi1 0).const_mul CV)).add
      ((hi1 1).const_mul CV))
      ((hwc.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp hΦc).mul hTc)))
        ).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    show ‖w y * (starRingEnd ℂ (Φ y) * transCx V Φ y).re‖ ≤
      CV * (w y * ‖Φ y‖ ^ 2) + CV * (w y * ‖pdCx 0 Φ y‖ ^ 2) + CV * (w y * ‖pdCx 1 Φ y‖ ^ 2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw.nonneg y)]
    have h1 := re_conj_mul_norm_le (Φ y) (transCx V Φ y)
    have h2 := norm_transCx_le V Φ CV hCV y (hV.bound y 0) (hV.bound y 1)
    have h3 : w y * |(starRingEnd ℂ (Φ y) * transCx V Φ y).re| ≤
        w y * (‖Φ y‖ * (CV * ‖pdCx 0 Φ y‖ + CV * ‖pdCx 1 Φ y‖)) :=
      mul_le_mul_of_nonneg_left (le_trans h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
        (hw.nonneg y)
    have h4 : ‖Φ y‖ * (CV * ‖pdCx 0 Φ y‖ + CV * ‖pdCx 1 Φ y‖) ≤
        CV * (‖Φ y‖ ^ 2 + ‖pdCx 0 Φ y‖ ^ 2 + ‖pdCx 1 Φ y‖ ^ 2) := by
      nlinarith [mul_nonneg hCV (sq_nonneg (‖Φ y‖ - ‖pdCx 0 Φ y‖)),
        mul_nonneg hCV (sq_nonneg (‖Φ y‖ - ‖pdCx 1 Φ y‖)),
        mul_nonneg hCV (sq_nonneg (‖pdCx 0 Φ y‖)), mul_nonneg hCV (sq_nonneg (‖pdCx 1 Φ y‖))]
    calc w y * |(starRingEnd ℂ (Φ y) * transCx V Φ y).re|
        ≤ w y * (‖Φ y‖ * (CV * ‖pdCx 0 Φ y‖ + CV * ‖pdCx 1 Φ y‖)) := h3
      _ ≤ w y * (CV * (‖Φ y‖ ^ 2 + ‖pdCx 0 Φ y‖ ^ 2 + ‖pdCx 1 Φ y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h4 (hw.nonneg y)
      _ = CV * (w y * ‖Φ y‖ ^ 2) + CV * (w y * ‖pdCx 0 Φ y‖ ^ 2) + CV * (w y * ‖pdCx 1 Φ y‖ ^ 2) := by
          ring
  have hPint : IntegrableOn (fun y => (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y) *
      ‖Φ y‖ ^ 2) (B0579.cell d) := by
    have hpk : ∀ k : Fin 2, ∀ y : ℝ × ℝ, |B0579.pd k w y| ≤ |K| * w y := fun k y =>
      le_trans (hw.grad y k) (mul_le_mul_of_nonneg_right (le_abs_self K) (hw.nonneg y))
    refine Integrable.mono' ((hi0.const_mul (2 * CV * |K|)))
      ((((hVk 0).mul (hpdw 0)).add ((hVk 1).mul (hpdw 1))).mul hNc).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    show ‖(V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y) * ‖Φ y‖ ^ 2‖ ≤
      2 * CV * |K| * (w y * ‖Φ y‖ ^ 2)
    have hs : |V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y| ≤ 2 * CV * |K| * w y :=
      calc |V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y|
          ≤ |V y 0 * B0579.pd 0 w y| + |V y 1 * B0579.pd 1 w y| := abs_add_le _ _
        _ = |V y 0| * |B0579.pd 0 w y| + |V y 1| * |B0579.pd 1 w y| := by
            rw [abs_mul, abs_mul]
        _ ≤ CV * (|K| * w y) + CV * (|K| * w y) :=
            add_le_add (mul_le_mul (hV.bound y 0) (hpk 0 y) (abs_nonneg _) hCV)
              (mul_le_mul (hV.bound y 1) (hpk 1 y) (abs_nonneg _) hCV)
        _ = 2 * CV * |K| * w y := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖Φ y‖ ^ 2)]
    calc |V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y| * ‖Φ y‖ ^ 2
        ≤ (2 * CV * |K| * w y) * ‖Φ y‖ ^ 2 := mul_le_mul_of_nonneg_right hs (by positivity)
      _ = 2 * CV * |K| * (w y * ‖Φ y‖ ^ 2) := by ring
  have hperF : ∀ y : ℝ × ℝ,
      (fun x => V x 0 * (w x * ‖Φ x‖ ^ 2)) (y.1 + d, y.2) = (fun x => V x 0 * (w x * ‖Φ x‖ ^ 2)) y := by
    intro y
    show V (y.1 + d, y.2) 0 * (w (y.1 + d, y.2) * ‖Φ (y.1 + d, y.2)‖ ^ 2) =
      V y 0 * (w y * ‖Φ y‖ ^ 2)
    rw [hV.periodic y, hw.periodic y, hper y]
  have hpsum : IntegrableOn (fun y => B0579.pd 0 (fun x => V x 0 * (w x * ‖Φ x‖ ^ 2)) y +
      B0579.pd 1 (fun x => V x 1 * (w x * ‖Φ x‖ ^ 2)) y) (B0579.cell d) :=
    ((hPint.add (hW.const_mul 2)).congr (ae_of_all _ fun y => (hpt y).symm))
  have hzero := cellDivZero d hd (fun x => V x 0 * (w x * ‖Φ x‖ ^ 2))
    (fun x => V x 1 * (w x * ‖Φ x‖ ^ 2)) (hF 0) (hF 1) hperF (hFint 1) hpsum
  have e : ∫ y in B0579.cell d, (B0579.pd 0 (fun x => V x 0 * (w x * ‖Φ x‖ ^ 2)) y +
      B0579.pd 1 (fun x => V x 1 * (w x * ‖Φ x‖ ^ 2)) y) =
      ∫ y in B0579.cell d, ((V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y) * ‖Φ y‖ ^ 2 +
        2 * (w y * (starRingEnd ℂ (Φ y) * transCx V Φ y).re)) :=
    integral_congr_ae (ae_of_all _ fun y => hpt y)
  have s1 := integral_add hPint (hW.const_mul 2)
  have s2 : ∫ y in B0579.cell d, 2 * (w y * (starRingEnd ℂ (Φ y) * transCx V Φ y).re) =
      2 * ∫ y in B0579.cell d, w y * (starRingEnd ℂ (Φ y) * transCx V Φ y).re :=
    integral_const_mul _ _
  linarith [hzero, e, s1, s2]

end UnforcedLeray.Short.IIIa.E0
