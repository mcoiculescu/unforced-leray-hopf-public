import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4_2
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowIntegral.RingBridgeReal
import UnforcedLeray.Lib.Axisymmetric.RingMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Analysis.Complex.Norm

/-!
# Part II-b, task `PartII-b:T09/4/2/6` (`RingBridgeC`)

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.

Complex case of the ring-chart bridge, from the signed real case `ringBridgeReal`
(`RingBridgeReal.lean`) by taking real and imaginary parts.  The integrability needed to commute
`re`/`im` with the inner and outer Bochner integrals comes from the finiteness of the weighted
phase lintegral of `‖F‖` (the lintegral form of `Axi.phaseAvg_ringChart`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Finiteness of the phase-integrated lintegral of a nonnegative periodic `G` with finite weighted
`L¹`-norm (copy of the private lemma in `RingBridgeReal.lean`). -/
private theorem ringChart_lintegral_ne_top_C (c ε : ℝ) (G : ℝ × (ℝ × ℝ) → ℝ) (hc : 0 < c)
    (hε : 0 < ε) (hG : Measurable G)
    (hper : ∀ s ξ η : ℝ, G (s, (ξ + c, η)) = G (s, (ξ, η)))
    (hfin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (G p) < ⊤) :
    ∫⁻ τ in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y : Space, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y)) ≠ ⊤ := by
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    rw [div_inv_eq_mul]; ring
  have hGm' : Measurable fun x : ℝ × (ℝ × ℝ) => ENNReal.ofReal (G x) :=
    ENNReal.measurable_ofReal.comp hG
  have hper' : ∀ s q η : ℝ, ENNReal.ofReal (G (s, (q + c, η)))
      = ENNReal.ofReal (G (s, (q, η))) := by
    intro s q η
    rw [hper s q η]
  have key : (ENNReal.ofReal (2 * ε * c))⁻¹ *
        ∫⁻ τ in Ioc 0 (2 * ε * c), ∫⁻ y, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y)) =
      ENNReal.ofReal (Real.pi * (ε⁻¹) ^ 2) *
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
          ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (G p) :=
    Axi.phaseAvg_ringChart hR hc hP _ hGm' hper'
  intro hZ
  have hlt : (ENNReal.ofReal (2 * ε * c))⁻¹ *
      ∫⁻ τ in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y : Space, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y)) < ⊤ := by
    rw [key]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  rw [hZ, ENNReal.mul_top (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)] at hlt
  exact lt_irrefl _ hlt

/-- Measurability of `x ↦ H (chart R x.1 x.2)` on `ℝ × Space`. -/
private theorem measurable_chartC {E : Type*} [MeasurableSpace E] (R : ℝ) {H : ℝ × (ℝ × ℝ) → E}
    (hH : Measurable H) :
    Measurable fun x : ℝ × Space => H (Axi.chart R x.1 x.2) := by
  refine hH.comp ?_
  exact ((Axi.measurable_age R).comp measurable_snd).prodMk
    ((Axi.measurable_phase R).prodMk ((Axi.measurable_trans R).comp measurable_snd))

/-- Measurability of the phase section `y ↦ H (chart R τ y)` (complex-valued `H`). -/
private theorem sec_measurableC (R : ℝ) {H : ℝ × (ℝ × ℝ) → ℂ}
    (hH : Measurable H) (τ : ℝ) :
    Measurable fun y : Space => H (Axi.chart R τ y) := by
  have h1 : Measurable fun y : Space => ((τ, y) : ℝ × Space) :=
    measurable_const.prodMk measurable_id
  have h2 := (measurable_chartC R hH).comp h1
  exact h2

/-- Measurability of the phase section `y ↦ H (chart R τ y)` (real-valued `H`). -/
private theorem sec_measurableR (R : ℝ) {H : ℝ × (ℝ × ℝ) → ℝ}
    (hH : Measurable H) (τ : ℝ) :
    Measurable fun y : Space => H (Axi.chart R τ y) := by
  have h1 : Measurable fun y : Space => ((τ, y) : ℝ × Space) :=
    measurable_const.prodMk measurable_id
  have h2 := (measurable_chartC R hH).comp h1
  exact h2

/-- Pointwise bound `‖re z‖ₑ ≤ ‖z‖ₑ`. -/
private theorem enorm_re_le_C (z : ℂ) : ‖z.re‖ₑ ≤ ‖z‖ₑ := by
  have h : ‖z.re‖ ≤ ‖z‖ := by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm z
  exact (ofReal_norm z.re).symm.le.trans ((ENNReal.ofReal_le_ofReal h).trans (ofReal_norm z).le)

/-- Pointwise bound `‖im z‖ₑ ≤ ‖z‖ₑ`. -/
private theorem enorm_im_le_C (z : ℂ) : ‖z.im‖ₑ ≤ ‖z‖ₑ := by
  have h : ‖z.im‖ ≤ ‖z‖ := by rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm z
  exact (ofReal_norm z.im).symm.le.trans ((ENNReal.ofReal_le_ofReal h).trans (ofReal_norm z).le)

theorem ringBridgeC : UnforcedLeray.Short.IIb.RingBridgeC := by
  intro c ε F hc hε hF hper hfin
  have hε' : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hw : Measurable fun p : ℝ × (ℝ × ℝ) => p.1 ^ (-(5 / 2 : ℝ)) :=
    measurable_fst.pow_const _
  -- the norm of `F`
  obtain ⟨G0, hG0⟩ : ∃ f : ℝ × (ℝ × ℝ) → ℝ, f = fun x => ‖F x‖ := ⟨_, rfl⟩
  have hG0m : Measurable G0 := by rw [hG0]; exact hF.norm
  have hG0per : ∀ s ξ η : ℝ, G0 (s, (ξ + c, η)) = G0 (s, (ξ, η)) := by
    intro s ξ η
    simp only [hG0, hper s ξ η]
  have hG0nn : ∀ x, 0 ≤ G0 x := fun x => by rw [hG0]; exact norm_nonneg _
  have hfinG : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (G0 p) < ⊤ := by
    refine lt_of_eq_of_lt (lintegral_congr fun p => ?_) hfin
    congr 1
    rw [hG0]
    exact ofReal_norm (F p)
  -- phase lintegral finiteness for `‖F‖`
  have hτfin := ringChart_lintegral_ne_top_C c ε G0 hc hε hG0m hG0per hfinG
  have hZm : Measurable fun τ : ℝ => ∫⁻ y : Space, ENNReal.ofReal (G0 (Axi.chart ε⁻¹ τ y)) :=
    (ENNReal.measurable_ofReal.comp (measurable_chartC ε⁻¹ hG0m)).lintegral_prod_right'
  have hpAE : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      ∫⁻ y : Space, ENNReal.ofReal (G0 (Axi.chart ε⁻¹ τ y)) < ⊤ :=
    ae_lt_top hZm hτfin
  -- a.e. integrability of the phase sections of `F`
  have hIntF : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      Integrable (fun y : Space => F (Axi.chart ε⁻¹ τ y)) := by
    filter_upwards [hpAE] with τ hτ
    refine ⟨(sec_measurableC ε⁻¹ hF τ).aestronglyMeasurable, ?_⟩
    have h3 : ∫⁻ y : Space, ‖F (Axi.chart ε⁻¹ τ y)‖ₑ
        = ∫⁻ y : Space, ENNReal.ofReal (G0 (Axi.chart ε⁻¹ τ y)) :=
      lintegral_congr fun y => by rw [hG0]; exact (ofReal_norm _).symm
    show ∫⁻ y : Space, ‖F (Axi.chart ε⁻¹ τ y)‖ₑ < ⊤
    rw [h3]
    exact hτ
  -- the phase average of `F` is integrable in `τ`
  have hφm : StronglyMeasurable (fun τ : ℝ => ∫ y : Space, F (Axi.chart ε⁻¹ τ y)) :=
    (measurable_chartC ε⁻¹ hF).stronglyMeasurable.integral_prod_right'
  have hφbound : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) (2 * ε * c))),
      ‖∫ y : Space, F (Axi.chart ε⁻¹ τ y)‖ ≤
        (∫⁻ y : Space, ENNReal.ofReal (G0 (Axi.chart ε⁻¹ τ y))).toReal := by
    filter_upwards [hIntF] with τ hτ
    have h1 : ‖∫ y : Space, F (Axi.chart ε⁻¹ τ y)‖ ≤ ∫ y : Space, ‖F (Axi.chart ε⁻¹ τ y)‖ :=
      norm_integral_le_integral_norm _
    have h2 : ∫ y : Space, ‖F (Axi.chart ε⁻¹ τ y)‖ = ∫ y : Space, G0 (Axi.chart ε⁻¹ τ y) := by
      congr 1
      funext y
      simp only [hG0]
    rw [h2] at h1
    refine h1.trans (le_of_eq ?_)
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => hG0nn _)
      (sec_measurableR ε⁻¹ hG0m τ).aestronglyMeasurable
  have hφint : Integrable (fun τ : ℝ => ∫ y : Space, F (Axi.chart ε⁻¹ τ y))
      (volume.restrict (Ioc (0 : ℝ) (2 * ε * c))) :=
    Integrable.mono' (integrable_toReal_of_lintegral_ne_top hZm.aemeasurable hτfin)
      hφm.aestronglyMeasurable hφbound
  -- the bridge identities for the real and imaginary parts
  have hG1m : Measurable fun x : ℝ × (ℝ × ℝ) => (F x).re := Complex.measurable_re.comp hF
  have hG2m : Measurable fun x : ℝ × (ℝ × ℝ) => (F x).im := Complex.measurable_im.comp hF
  have hG1per : ∀ s ξ η : ℝ, (F (s, (ξ + c, η))).re = (F (s, (ξ, η))).re := by
    intro s ξ η; rw [hper s ξ η]
  have hG2per : ∀ s ξ η : ℝ, (F (s, (ξ + c, η))).im = (F (s, (ξ, η))).im := by
    intro s ξ η; rw [hper s ξ η]
  have hG1fin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖(F p).re‖ₑ < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hfin
    exact mul_le_mul_of_nonneg_left (enorm_re_le_C (F p)) (by positivity)
  have hG2fin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖(F p).im‖ₑ < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hfin
    exact mul_le_mul_of_nonneg_left (enorm_im_le_C (F p)) (by positivity)
  have hR1 := ringBridgeReal c ε (fun x => (F x).re) hc hε hG1m hG1per hG1fin
  have hR2 := ringBridgeReal c ε (fun x => (F x).im) hc hε hG2m hG2per hG2fin
  -- integrability of the weighted cell integrand
  have hBint : Integrable (fun p : ℝ × (ℝ × ℝ) => ((p.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * F p)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell c)) := by
    refine ⟨((Complex.measurable_ofReal.comp hw).mul hF).aestronglyMeasurable, ?_⟩
    have hbd : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ‖((p.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * F p‖ₑ ≤
          ENNReal.ofReal c * (ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖F p‖ₑ) := by
      intro p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      have hw0 : 0 ≤ p.1 ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hp1.le _
      have key : ‖((p.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * F p‖ₑ =
          ENNReal.ofReal (p.1 ^ (-(5 / 2 : ℝ))) * ‖F p‖ₑ := by
        rw [enorm_mul]
        congr 1
        exact (ofReal_norm ((p.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)).symm.trans
          (by rw [Complex.norm_real, Real.norm_of_nonneg hw0])
      have hwc : ENNReal.ofReal (p.1 ^ (-(5 / 2 : ℝ))) =
          ENNReal.ofReal c * ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) := by
        rw [← ENNReal.ofReal_mul hc.le, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
      rw [key, hwc]
      exact le_of_eq (by ring)
    have hlin : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal c * (ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ‖F p‖ₑ) < ⊤ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hlin
    filter_upwards [ae_restrict_mem hS] with p hp
    exact hbd p hp
  -- real and imaginary parts of the weighted cell integral
  have hBre : (∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, ((p.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * F p).re
      = ∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, p.1 ^ (-(5 / 2 : ℝ)) * (F p).re := by
    refine (integral_re hBint).symm.trans (integral_congr_ae (ae_of_all _ fun p => ?_))
    exact Complex.re_ofReal_mul _ _
  have hBim : (∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, ((p.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * F p).im
      = ∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, p.1 ^ (-(5 / 2 : ℝ)) * (F p).im := by
    refine (integral_im hBint).symm.trans (integral_congr_ae (ae_of_all _ fun p => ?_))
    exact Complex.im_ofReal_mul _ _
  -- inner and outer real/imaginary parts of the phase average
  have hAre : (∫ τ in Ioc (0 : ℝ) (2 * ε * c), ∫ y : Space, F (Axi.chart ε⁻¹ τ y)).re
      = ∫ τ in Ioc (0 : ℝ) (2 * ε * c), ∫ y : Space, (F (Axi.chart ε⁻¹ τ y)).re := by
    refine (integral_re hφint).symm.trans (integral_congr_ae ?_)
    filter_upwards [hIntF] with τ hτ
    exact (integral_re hτ).symm
  have hAim : (∫ τ in Ioc (0 : ℝ) (2 * ε * c), ∫ y : Space, F (Axi.chart ε⁻¹ τ y)).im
      = ∫ τ in Ioc (0 : ℝ) (2 * ε * c), ∫ y : Space, (F (Axi.chart ε⁻¹ τ y)).im := by
    refine (integral_im hφint).symm.trans (integral_congr_ae ?_)
    filter_upwards [hIntF] with τ hτ
    exact (integral_im hτ).symm
  refine Complex.ext ?_ ?_
  · rw [Complex.smul_re, smul_eq_mul, Complex.re_ofReal_mul, hAre, hBre]
    exact hR1
  · rw [Complex.smul_im, smul_eq_mul, Complex.im_ofReal_mul, hAim, hBim]
    exact hR2

end UnforcedLeray.Short.IIb
