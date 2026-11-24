import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.RepChart.Chart

/-!
# `RepChart/Chart2`: `ρ_b^{-1/2}‖multMaj R V f‖_{H_T} ≤ ρ_b^{-1/2}π^{-1/2}R⁻¹‖G‖_{L²_τL²}`
(source 2683-2689, 2698-2713)
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace RC

theorem rpow_alg {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ENNReal.ofReal (c⁻¹ * s ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (s⁻¹) ^ 2 =
      ENNReal.ofReal (c⁻¹ * s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal s⁻¹ := by
  rw [← ENNReal.ofReal_pow (inv_nonneg.2 hs.le), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : s ^ (-3 / 2 : ℝ) = s ^ (-1 / 2 : ℝ) * s⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hs]; norm_num
  rw [this]; ring

theorem htMaj_multMaj_le {R c ρb : ℝ} (hR : 0 < R) (hc : 0 < c) (hρ : 0 < ρb)
    {V : ℝ → Space → Space}
    (hMm : Measurable (Function.uncurry fun τ y => ENNReal.ofReal (merTr V τ y)))
    (hMper : ∀ τ y, merTr V (τ + 2 * c / R) y = merTr V τ y)
    {f : ℝ → Space → ℝ≥0∞} (hf : ChartGood (2 * c / R) f) :
    htMaj c ρb (multMaj R V f) ≤
      ENNReal.ofReal (Real.sqrt (ρb⁻¹ * Real.pi⁻¹) * R⁻¹) *
        IIIa.ltauLq (2 * c / R) 2 (fun τ y => ENNReal.ofReal (merTr V τ y) * f τ y) := by
  set G : ℝ → Space → ℝ≥0∞ := fun τ y => ENNReal.ofReal (merTr V τ y) * f τ y with hG
  have hGm : Measurable (Function.uncurry G) := hMm.mul hf.1
  have hGper : ∀ τ y, G (τ + 2 * c / R) y = G τ y := by
    intro τ y; simp only [hG, hMper, hf.2.1]
  have hGaxi : ∀ τ (y y' : Space), y' 2 = y 2 → y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 →
      G τ y' = G τ y := by
    intro τ y y' h2 h01
    have hϱ : ϱ y' = ϱ y := by unfold ϱ; rw [h01]
    simp only [hG, merTr, hϱ, h2, hf.2.2 τ y y' h2 h01]
  clear_value G
  have hphys := chartPhysL2 R c hR hc G hGm hGper hGaxi
  set L := IIIa.ltauLq (2 * c / R) 2 G with hL
  have hGcm : Measurable fun p : Chart => G (NearInst.chartTau R p) (NearInst.chartY R p) :=
    hGm.comp ((TC.measurable_chartTau' R).prodMk (TC.measurable_chartY' R))
  have hW : Measurable fun p : Chart => ENNReal.ofReal p.1⁻¹ := 
    ENNReal.measurable_ofReal.comp measurable_fst.inv
  -- the age integral
  have E1 : ∫⁻ p, multMaj R V f p ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) =
      ∫⁻ p, (ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau R p) (NearInst.chartY R p)) ^ (2 : ℝ)
        ∂(ageμ c (-1 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_ageμ_mem hc (-1 / 2)] with p hp
    rw [multMaj_eq hR V f hp.1, hG]
  have E2 : ∫⁻ p, (ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau R p) (NearInst.chartY R p)) ^ (2 : ℝ)
        ∂(ageμ c (-1 / 2)) =
      ∫⁻ p, ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau R p) (NearInst.chartY R p) ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2)) := by
    have m1 : Measurable fun p : Chart =>
        (ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau R p) (NearInst.chartY R p)) ^ (2 : ℝ) :=
      (hW.mul hGcm).pow_const _
    have m2 : Measurable fun p : Chart =>
        ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau R p) (NearInst.chartY R p) ^ (2 : ℝ) :=
      hW.mul (hGcm.pow_const _)
    rw [lintegral_ageμ hc _ m1, lintegral_ageμ hc _ m2]
    refine setLIntegral_congr_fun (measurableSet_halfCell c) (fun p hp => ?_)
    have hs : 0 < p.1 := hp.1
    simp only [ENNReal.rpow_two, mul_pow]
    rw [← mul_assoc, rpow_alg hc hs, mul_assoc]
  have E3 : ENNReal.ofReal Real.pi * ∫⁻ p, ENNReal.ofReal p.1⁻¹ *
        G (NearInst.chartTau R p) (NearInst.chartY R p) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
      ENNReal.ofReal (R⁻¹ ^ 2) * L ^ (2 : ℝ) := by
    have := hphys
    unfold srcMeasure at this
    rwa [lintegral_smul_measure, smul_eq_mul] at this
  have hπ : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.2 Real.pi_pos).ne'
  have E4 : ∫⁻ p, multMaj R V f p ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) ≤
      (ENNReal.ofReal Real.pi)⁻¹ * (ENNReal.ofReal (R⁻¹ ^ 2) * L ^ (2 : ℝ)) := by
    rw [E1, E2]
    exact (ENNReal.mul_le_iff_le_inv hπ ENNReal.ofReal_ne_top).1 E3
  unfold htMaj htRhoMeasure
  rw [lintegral_smul_measure, smul_eq_mul]
  have hκ : (Real.sqrt (ρb⁻¹ * Real.pi⁻¹) * R⁻¹) ^ 2 = ρb⁻¹ * Real.pi⁻¹ * R⁻¹ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have key : ENNReal.ofReal ρb⁻¹ * ((ENNReal.ofReal Real.pi)⁻¹ *
      (ENNReal.ofReal (R⁻¹ ^ 2) * L ^ (2 : ℝ))) =
      (ENNReal.ofReal (Real.sqrt (ρb⁻¹ * Real.pi⁻¹) * R⁻¹) * L) ^ (2 : ℝ) := by
    simp only [ENNReal.rpow_two, mul_pow]
    rw [← ENNReal.ofReal_pow (by positivity), hκ, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos Real.pi_pos]
    ring
  calc (ENNReal.ofReal ρb⁻¹ * ∫⁻ p, multMaj R V f p ^ (2 : ℝ) ∂(ageμ c (-1 / 2))) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ρb⁻¹ * ((ENNReal.ofReal Real.pi)⁻¹ *
          (ENNReal.ofReal (R⁻¹ ^ 2) * L ^ (2 : ℝ)))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (mul_le_mul' le_rfl E4) (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (ρb⁻¹ * Real.pi⁻¹) * R⁻¹) * L := by
        rw [key, ← ENNReal.rpow_mul]; norm_num

end RC

end UnforcedLeray.Short.PartIIIb.Concrete

end
