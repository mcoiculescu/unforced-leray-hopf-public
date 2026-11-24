import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4_2
import UnforcedLeray.Lib.Axisymmetric.RingMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Part II-b, task `PartII-b:T09/4/2/4` (`RingBridgeNN`)

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.

Nonnegative case of the ring-chart bridge: `Axi.phaseAvg_ringChart` (`RingMeasure.lean:229`) with
`R = ε⁻¹`, `P = 2εc = 2c/R`, transported from `ENNReal` to real Bochner integrals.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem ringBridgeNN : UnforcedLeray.Short.IIb.RingBridgeNN := by
  intro c ε G hc hε hG hG0 hper hfin
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP0 : (0 : ℝ) < 2 * ε * c := by positivity
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
  have hZfin : ∫⁻ τ in Ioc 0 (2 * ε * c), ∫⁻ y, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y)) ≠ ⊤ := by
    intro hZ
    have hlt : (ENNReal.ofReal (2 * ε * c))⁻¹ *
        ∫⁻ τ in Ioc 0 (2 * ε * c), ∫⁻ y, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y)) < ⊤ := by
      rw [key]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
    rw [hZ, ENNReal.mul_top (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)] at hlt
    exact lt_irrefl _ hlt
  have hGt : Measurable fun x : ℝ × Space => G (Axi.chart ε⁻¹ x.1 x.2) := by
    refine hG.comp ?_
    exact ((Axi.measurable_age ε⁻¹).comp measurable_snd).prodMk
      ((Axi.measurable_phase ε⁻¹).prodMk ((Axi.measurable_trans ε⁻¹).comp measurable_snd))
  have hZmeas : Measurable fun τ : ℝ => ∫⁻ y, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y)) :=
    (ENNReal.measurable_ofReal.comp hGt).lintegral_prod_right'
  have hinner : ∀ τ : ℝ, ∫ y : Space, G (Axi.chart ε⁻¹ τ y) =
      (∫⁻ y, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y))).toReal := by
    intro τ
    refine integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hG0 _) ?_
    exact (hGt.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hZr : ∫ τ in Ioc (0 : ℝ) (2 * ε * c), ∫ y : Space, G (Axi.chart ε⁻¹ τ y) =
      (∫⁻ τ in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y))).toReal := by
    calc ∫ τ in Ioc (0 : ℝ) (2 * ε * c), ∫ y : Space, G (Axi.chart ε⁻¹ τ y)
        = ∫ τ in Ioc (0 : ℝ) (2 * ε * c),
            (∫⁻ y, ENNReal.ofReal (G (Axi.chart ε⁻¹ τ y))).toReal :=
          integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = _ := integral_toReal hZmeas.aemeasurable (ae_lt_top hZmeas hZfin)
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hYeq : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (G p) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal (c⁻¹ * (p.1 ^ (-(5 / 2 : ℝ)) * G p)) := by
    refine setLIntegral_congr_fun hS fun p hp => ?_
    have hpos : (0 : ℝ) < p.1 := hp.1
    have hnn : 0 ≤ c⁻¹ * p.1 ^ (-(5 / 2 : ℝ)) :=
      mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hpos.le _)
    rw [← ENNReal.ofReal_mul hnn]
    congr 1
    ring
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell c)]
      (fun p : ℝ × (ℝ × ℝ) => c⁻¹ * (p.1 ^ (-(5 / 2 : ℝ)) * G p)) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    have hpos : (0 : ℝ) < p.1 := hp.1
    exact mul_nonneg (inv_nonneg.2 hc.le)
      (mul_nonneg (Real.rpow_nonneg hpos.le _) (hG0 p))
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) => c⁻¹ * (p.1 ^ (-(5 / 2 : ℝ)) * G p))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell c)) :=
    (measurable_const.mul ((measurable_fst.pow_const _).mul hG)).aestronglyMeasurable
  have hYr : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c,
        ENNReal.ofReal (c⁻¹ * (p.1 ^ (-(5 / 2 : ℝ)) * G p))).toReal =
      c⁻¹ * ∫ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, p.1 ^ (-(5 / 2 : ℝ)) * G p := by
    have h := integral_eq_lintegral_of_nonneg_ae hnonneg hmeas
    rw [← h, integral_const_mul]
  have k2 := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hP0.le,
    ENNReal.toReal_ofReal (by positivity)] at k2
  rw [hYeq, hYr] at k2
  rw [hZr, k2]
  ring

end UnforcedLeray.Short.IIb
