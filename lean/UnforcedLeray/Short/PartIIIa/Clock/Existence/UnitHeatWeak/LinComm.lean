import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatResponseContinuity

/-!
# Part III-a, `PartIII-a:T21/3/2/2/1`: the cell pairing commutes with the Duhamel integral

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Proves `UnitHeatLinComm` (`Sub/PartIIIa_T21_3_2_2.lean`): for a cylinder test `ψ`, the pairing
`w ↦ ∫_cell vortFn w * ψ` is a continuous linear functional on `ActualVorticity`, so it commutes
with the interval Bochner integral `∫_a^t S(t-r) (F r) dr`.

Integrability and measurability of `r ↦ S(t-r) (F r)` come from the operator bound
`‖S θ‖ ≤ K θ^{-1/2}` for `0 < θ ≤ 1` and joint continuity of `(θ, F) ↦ S θ F` at positive ages.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- A uniform constant for the physical short-age response bound `‖S θ‖ ≤ K θ^{-1/2}`. -/
theorem exists_norm_response_le {c m : ℝ} [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m) :
    ∃ K : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) θ‖ ≤ K * θ ^ (-(1 / 2 : ℝ)) :=
  ⟨(actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).C₀,
    fun θ hθ hθ1 => (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).norm_S_le
      θ hθ hθ1⟩

/-- Along a continuous flux path, the physical response `r ↦ S(t-r) (F r)` is continuous on the
open interval `(a, t)`. -/
theorem continuousOn_pathResponse {c m : ℝ} [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m)
    {a b t : ℝ} (F : ℝ → ActualFlux (c := c) (m := m)) (hF : ContinuousOn F (Icc a b))
    (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ a + 1) :
    ContinuousOn (fun r => actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r))
      (Ioo a t) := by
  intro r0 hr0
  obtain ⟨hr0a, hr0t⟩ := hr0
  obtain ⟨K, hK⟩ := exists_norm_response_le (c := c) (m := m) hc1 hm
  have hK0 : 0 ≤ K := by
    have h := hK 1 one_pos le_rfl
    rw [Real.one_rpow, mul_one] at h
    exact (norm_nonneg (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) 1)).trans h
  have hθ0 : 0 < t - r0 := by linarith
  have hθ0' : t - r0 < 1 := by linarith
  have hθ0half : 0 < (t - r0) / 2 := by linarith
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = K * ((t - r0) / 2) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hcontF : ContinuousAt F r0 :=
    hF.continuousAt (Icc_mem_nhds hr0a (by linarith))
  have hFt : Tendsto (fun r => ‖F r - F r0‖) (𝓝 r0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hcontF.tendsto
  have hcontS : ContinuousAt
      (fun θ : ℝ => actualWeightedHeatResponse (c := c) (m := m) (hm := hm) θ (F r0))
      (t - r0) :=
    ((continuousOn_actualWeightedHeatResponse_apply hc1 hm (F r0)).mono
      Ioo_subset_Ioc_self).continuousAt (Ioo_mem_nhds hθ0 hθ0')
  have hSt : Tendsto (fun r =>
      ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r0) -
        actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r0) (F r0)‖)
      (𝓝 r0) (𝓝 0) := by
    have hsub : ContinuousAt (fun r : ℝ => t - r) r0 := by fun_prop
    have hc : ContinuousAt
        (fun r => actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r0)) r0 :=
      hcontS.comp hsub
    exact tendsto_iff_norm_sub_tendsto_zero.1 hc
  have hev : ∀ᶠ r in 𝓝 r0,
      ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r) -
          actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r0) (F r0)‖ ≤
        Kc * ‖F r - F r0‖ +
          ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r0) -
            actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r0) (F r0)‖ := by
    filter_upwards [Ioo_mem_nhds hr0a hr0t, Metric.ball_mem_nhds r0 hθ0half] with r hr hball
    have hdist : |r - r0| < (t - r0) / 2 := by
      have := Metric.mem_ball.1 hball
      rwa [Real.dist_eq] at this
    obtain ⟨hra, hrt⟩ := hr
    obtain ⟨hd1, hd2⟩ := abs_lt.1 hdist
    have hθpos : 0 < t - r := by linarith
    have hθ1 : t - r ≤ 1 := by linarith
    have hθhalf : (t - r0) / 2 ≤ t - r := by linarith
    have hnormS : ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r)‖ ≤ Kc := by
      have h1 := hK (t - r) hθpos hθ1
      have h2 : (t - r) ^ (-(1 / 2 : ℝ)) ≤ ((t - r0) / 2) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hθ0half hθhalf (by norm_num)
      rw [hKc]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hK0)
    have hid : actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r) -
          actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r0) (F r0) =
        actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r - F r0) +
          (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r0) -
            actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r0) (F r0)) := by
      rw [map_sub]
      abel
    rw [hid]
    have h1 : ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r - F r0)‖ ≤
        Kc * ‖F r - F r0‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hnormS (norm_nonneg _))
    exact (norm_add_le _ _).trans (add_le_add h1 le_rfl)
  have hA : Tendsto (fun r =>
      Kc * ‖F r - F r0‖ +
        ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r0) -
          actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r0) (F r0)‖)
      (𝓝 r0) (𝓝 0) := by
    have h := (hFt.const_mul Kc).add hSt
    rw [mul_zero, add_zero] at h
    exact h
  have hsq : Tendsto (fun r =>
      ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r) -
          actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r0) (F r0)‖)
      (𝓝 r0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) hev hA
  exact ContinuousAt.continuousWithinAt (tendsto_iff_norm_sub_tendsto_zero.2 hsq)

/-- (N4) The cell pairing with a cylinder test commutes with the Duhamel Bochner integral. -/
theorem unitHeatLinComm : UnforcedLeray.Short.IIIa.Exist.UnitHeatLinComm := by
  intro c m _ hc1 hm
  haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
  intro F a b hab hb hF ψ hψ t ht
  have hat : a ≤ t := ht.1
  have htb : t ≤ b := ht.2
  obtain ⟨K, hK⟩ := exists_norm_response_le (c := c) (m := m) hc1 hm
  have hK0 : 0 ≤ K := by
    have h := hK 1 one_pos le_rfl
    rw [Real.one_rpow, mul_one] at h
    exact (norm_nonneg (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) 1)).trans h
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hF
  have hN : ∀ r ∈ Ioo a t, ‖F r‖ ≤ max M 0 := fun r hr =>
    (hM r ⟨hr.1.le, hr.2.le.trans htb⟩).trans (le_max_left _ _)
  have hint : IntervalIntegrable
      (fun r => actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r))
      volume a t := by
    refine (intervalIntegrable_iff_integrableOn_Ioo_of_le hat).2 ?_
    have hg0 : IntervalIntegrable (fun r : ℝ => (t - r) ^ (-(1 / 2 : ℝ))) volume a t := by
      have h0 := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - a)
        (r := -(1 / 2 : ℝ)) (by norm_num)
      have h1 := h0.comp_sub_left t
      simp only [sub_zero, sub_sub_cancel] at h1
      exact h1.symm
    have hg : IntegrableOn (fun r => (K * max M 0) * (t - r) ^ (-(1 / 2 : ℝ))) (Ioo a t) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hat).1 (hg0.const_mul (K * max M 0))
    refine Integrable.mono' hg
      ((continuousOn_pathResponse (c := c) (m := m) hc1 hm F hF hat htb hb).aestronglyMeasurable
        measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have h1 := hK (t - r) (by linarith [hr.2]) (by linarith [hr.1])
    calc ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r)‖
        ≤ ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r)‖ * ‖F r‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * (t - r) ^ (-(1 / 2 : ℝ))) * max M 0 :=
          mul_le_mul h1 (hN r hr) (norm_nonneg _)
            (mul_nonneg hK0 (Real.rpow_nonneg (by linarith [hr.2]) _))
      _ = (K * max M 0) * (t - r) ^ (-(1 / 2 : ℝ)) := by ring
  let ℓ : ActualVorticity (c := c) (m := m) hm →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.B0579.testH1 c (-m) hψ)).comp
      ((UnforcedLeray.B0579.sourceCLM c m).comp
        (zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m)).subtypeL)
  have hℓ : ∀ w : ActualVorticity (c := c) (m := m) hm,
      ℓ w = ∫ x in UnforcedLeray.B0579.cell c, vortFn hm w x * ψ x :=
    fun w => UnforcedLeray.B0579.toDistribution_sourceCLM c m w.1 ⟨ψ, hψ⟩
  calc ∫ x in UnforcedLeray.B0579.cell c,
        vortFn hm (∫ r in a..t,
          (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S (t - r) (F r)) x
          * ψ x
      = ℓ (∫ r in a..t,
          actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r)) :=
        (hℓ _).symm
    _ = ∫ r in a..t, ℓ (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (t - r) (F r)) :=
        (ℓ.intervalIntegral_comp_comm hint).symm
    _ = ∫ r in a..t, ∫ x in UnforcedLeray.B0579.cell c,
          vortFn hm ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S
            (t - r) (F r)) x * ψ x :=
        intervalIntegral.integral_congr (fun r _ => hℓ _)

end UnforcedLeray.Short.IIIa.Exist
