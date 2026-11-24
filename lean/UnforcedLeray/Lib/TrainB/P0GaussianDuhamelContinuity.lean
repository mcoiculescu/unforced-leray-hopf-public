import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelLag

/-!
# Positive-time continuity of the actual nonlinear Volterra integral

Reversing source time to heat lag turns the moving square-root singularity into a fixed integrable
majorant. Dominated convergence then proves continuity at every positive target time.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

/-- Lag integrand cut off to the causal interval `(0,t)`. -/
def projectedHeatDuhamelLagIntegrand {c ν : ℝ} (hc : 0 < c)
    (F : ContinuousMap ℝ (TensorH3 c)) (t ρ : ℝ) : VectorH3 c :=
  (Ioo 0 t).indicator (fun x => projectedHeatDuhamelLagField (ν := ν) hc F t x) ρ

private theorem toReal_ofReal_trainHeatCoeff_cont {θ : ℝ} (hθ : 0 < θ) :
    (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
      ENNReal.ofReal (heatDivL2Coeff θ)).toReal =
      ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
        heatDivL2Coeff θ := by
  have hK : 0 ≤ ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ := norm_nonneg _
  have hcoeff : 0 ≤ heatDivL2Coeff θ := by
    unfold heatDivL2Coeff
    positivity
  rw [← ENNReal.ofReal_mul hK]
  exact ENNReal.toReal_ofReal (mul_nonneg hK hcoeff)

/-- Positive-time continuity of the actual projected nonlinear Duhamel integral for a globally
bounded continuous tensor path. -/
theorem continuousAt_projectedHeatDuhamelIntegral_pos {c ν t₀ M : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (ht₀ : 0 < t₀) (hM : 0 ≤ M)
    (F : ContinuousMap ℝ (TensorH3 c)) (hF : ∀ r, ‖F r‖ ≤ M) :
    ContinuousAt (fun t => projectedHeatDuhamelIntegral (ν := ν) hc F t) t₀ := by
  let T : ℝ := t₀ + 1
  have hT : t₀ < T := by dsimp [T]; linarith
  have hTpos : 0 < T := lt_trans ht₀ hT
  let μ : Measure ℝ := volume.restrict (Ioo 0 T)
  let K : ℝ := ‖(UnforcedLeray.Train.toVecL :
    UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖
  let H : ℝ → ℝ := fun ρ => (M * K) * heatDivL2Coeff (ν * ρ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcoeffInt : IntervalIntegrable
      (fun ρ : ℝ => heatDivL2Coeff (ν * ρ)) volume 0 T := by
    have hI := integrable_heatDivL2Coeff_Ioo hν hTpos
    have hInterval :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hTpos.le).mpr hI
    have hflip := hInterval.comp_sub_left T
    simpa [sub_sub_cancel] using hflip.symm
  have hHInt : Integrable H μ := by
    dsimp [H, μ, K]
    have hRestr : Integrable (fun ρ : ℝ => heatDivL2Coeff (ν * ρ))
        (volume.restrict (Ioo 0 T)) := by
      exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hTpos.le).1 hcoeffInt
    simpa using hRestr.const_mul
      (M * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖)
  have hHnonneg : ∀ᵐ ρ ∂μ, 0 ≤ H ρ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
    have hθ : 0 < ν * ρ := mul_pos hν hρ.1
    have hcθ : 0 ≤ heatDivL2Coeff (ν * ρ) := by
      unfold heatDivL2Coeff
      positivity
    dsimp [H]
    positivity
  have hLagCont : ∀ t : ℝ, ContinuousOn
      (fun ρ => projectedHeatDuhamelLagField (ν := ν) hc F t ρ) (Ioi 0) := by
    intro t
    intro ρ hρ
    let r : ℝ := t - ρ
    have hρpos : 0 < ρ := by simpa using hρ
    have hr : r < t := by dsimp [r]; linarith
    have hsource : ContinuousAt
        (fun q => projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F q) r :=
      continuousAt_projectedHeatDuhamelOrbit hc hν hr F.continuous.continuousAt
    have harg : ContinuousAt (fun ρ : ℝ => t - ρ) ρ := by fun_prop
    have hcomp := ContinuousAt.comp
      (g := fun q => projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F q)
      (f := fun ρ : ℝ => t - ρ) hsource harg
    have heq : (fun ρ : ℝ => projectedHeatDuhamelLagField (ν := ν) hc F t ρ) =
        fun ρ => projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F (t - ρ) := by
      funext ρ
      simp [projectedHeatDuhamelLagField, projectedHeatDuhamelOrbit]
    rw [heq]
    exact hcomp.continuousWithinAt
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (projectedHeatDuhamelLagIntegrand (ν := ν) hc F t) μ := by
    intro t
    have hcont : ContinuousOn
        (fun ρ => projectedHeatDuhamelLagField (ν := ν) hc F t ρ) (Ioo 0 T) :=
      (hLagCont t).mono fun ρ hρ => hρ.1
    have hlagAEM : AEStronglyMeasurable
        (fun ρ => projectedHeatDuhamelLagField (ν := ν) hc F t ρ) μ :=
      hcont.aestronglyMeasurable_of_isSeparable measurableSet_Ioo
        (TopologicalSpace.IsSeparable.of_separableSpace (Ioo 0 T))
    exact hlagAEM.indicator measurableSet_Ioo
  have hbound : ∀ t : ℝ, ∀ᵐ ρ ∂μ,
      ‖projectedHeatDuhamelLagIntegrand (ν := ν) hc F t ρ‖ ≤ H ρ := by
    intro t
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
    by_cases hmem : ρ ∈ Ioo 0 t
    · have hρ0 : 0 < ρ := hmem.1
      have hθ : 0 < ν * ρ := mul_pos hν hρ0
      have hcoeff : 0 ≤ heatDivL2Coeff (ν * ρ) := by
        unfold heatDivL2Coeff
        positivity
      have hreal := toReal_ofReal_trainHeatCoeff_cont hθ
      have hheat := norm_actualHeatDivH3_le hc hθ (F (t - ρ))
      have hcontract :
          ‖projectedHeatDuhamelLagField (ν := ν) hc F t ρ‖ ≤
            ‖actualHeatDivH3Orbit hc (F (t - ρ)) (ν * ρ)‖ := by
        change ‖P0H3CLM hc
          (actualHeatDivH3Orbit hc (F (t - ρ)) (ν * ρ))‖ ≤ _
        exact P0H3CLM_apply_norm_le hc _
      have hactual : actualHeatDivH3Orbit hc (F (t - ρ)) (ν * ρ) =
          actualHeatDivH3CLM hc hθ (F (t - ρ)) := by
        simp [actualHeatDivH3Orbit, hθ]
      have hscaled : ‖actualHeatDivH3CLM hc hθ (F (t - ρ))‖ ≤
          (K * heatDivL2Coeff (ν * ρ)) * ‖F (t - ρ)‖ := by
        rw [hreal] at hheat
        simpa [K, mul_assoc] using hheat
      have hFbound := hF (t - ρ)
      simp [projectedHeatDuhamelLagIntegrand, hmem]
      calc
        ‖projectedHeatDuhamelLagField (ν := ν) hc F t ρ‖ ≤
            (K * heatDivL2Coeff (ν * ρ)) * ‖F (t - ρ)‖ := by
              rw [hactual] at hcontract
              exact hcontract.trans hscaled
        _ ≤ (K * heatDivL2Coeff (ν * ρ)) * M :=
          mul_le_mul_of_nonneg_left hFbound (mul_nonneg hK hcoeff)
        _ = H ρ := by dsimp [H]; ring
    · simp [projectedHeatDuhamelLagIntegrand, hmem, H]
      exact mul_nonneg (mul_nonneg hM hK) (le_of_lt (by
        have hρ0 := hρ.1
        unfold heatDivL2Coeff
        positivity))
  let l := 𝓝[Icc 0 T] t₀
  have hne : ∀ᵐ ρ ∂μ, ρ ≠ t₀ := by
    have hneV : ∀ᵐ ρ : ℝ ∂volume, ρ ≠ t₀ := by
      simp [ae_iff, measure_singleton]
    exact ae_restrict_of_ae hneV
  have hlim : ∀ᵐ ρ ∂μ, Tendsto
      (fun t => projectedHeatDuhamelLagIntegrand (ν := ν) hc F t ρ) l
      (𝓝 (projectedHeatDuhamelLagIntegrand (ν := ν) hc F t₀ ρ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with ρ hρ hρne
    rcases lt_or_gt_of_ne hρne with hρt | htρ
    · have hρpos : 0 < ρ := hρ.1
      have hθ : 0 < ν * ρ := mul_pos hν hρpos
      have hFcomp : ContinuousAt (fun t : ℝ => F (t - ρ)) t₀ := by
        exact ContinuousAt.comp (g := F) (f := fun t : ℝ => t - ρ)
          F.continuous.continuousAt (by fun_prop)
      have hactualCont : ContinuousAt
          (fun t : ℝ => actualHeatDivH3CLM hc hθ (F (t - ρ))) t₀ :=
        ContinuousAt.comp (g := actualHeatDivH3CLM hc hθ)
          (f := fun t : ℝ => F (t - ρ))
          (actualHeatDivH3CLM hc hθ).continuous.continuousAt hFcomp
      have hlagCont : ContinuousAt
          (fun t : ℝ => projectedHeatDuhamelLagField (ν := ν) hc F t ρ) t₀ := by
        have hcomp : ContinuousAt
            (fun t : ℝ => P0H3CLM hc
              (actualHeatDivH3CLM hc hθ (F (t - ρ)))) t₀ :=
          ContinuousAt.comp (g := P0H3CLM hc)
            (f := fun t : ℝ => actualHeatDivH3CLM hc hθ (F (t - ρ)))
            (P0H3CLM hc).continuous.continuousAt hactualCont
        have heq : (fun t : ℝ => projectedHeatDuhamelLagField (ν := ν) hc F t ρ) =
            fun t => P0H3CLM hc (actualHeatDivH3CLM hc hθ (F (t - ρ))) := by
          funext t
          simp [projectedHeatDuhamelLagField, actualHeatDivH3Orbit, hθ]
        simpa only [heq] using hcomp
      have hnear : ∀ᶠ t in l, ρ < t := by
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hρt)] with t ht
        exact ht
      have hEq : ∀ᶠ t in l,
          projectedHeatDuhamelLagIntegrand (ν := ν) hc F t ρ =
            projectedHeatDuhamelLagField (ν := ν) hc F t ρ := by
        filter_upwards [hnear] with t ht
        simp [projectedHeatDuhamelLagIntegrand, hρ.1, ht]
      have htarget : projectedHeatDuhamelLagIntegrand (ν := ν) hc F t₀ ρ =
          projectedHeatDuhamelLagField (ν := ν) hc F t₀ ρ := by
        simp [projectedHeatDuhamelLagIntegrand, hρ.1, hρt]
      rw [htarget]
      have hEq' : (fun t : ℝ => projectedHeatDuhamelLagField (ν := ν) hc F t ρ) =ᶠ[l]
          (fun t => projectedHeatDuhamelLagIntegrand (ν := ν) hc F t ρ) :=
        hEq.mono fun _ h => h.symm
      have hlagTend : Tendsto
          (fun t : ℝ => projectedHeatDuhamelLagField (ν := ν) hc F t ρ) l
          (𝓝 (projectedHeatDuhamelLagField (ν := ν) hc F t₀ ρ)) :=
        hlagCont.tendsto.mono_left nhdsWithin_le_nhds
      exact hlagTend.congr' hEq'
    · have hnear : ∀ᶠ t in l, t < ρ := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds htρ)] with t ht
        exact ht
      have hEq : ∀ᶠ t in l,
          projectedHeatDuhamelLagIntegrand (ν := ν) hc F t ρ = 0 := by
        filter_upwards [hnear] with t ht
        simp [projectedHeatDuhamelLagIntegrand, not_lt.mpr (le_of_lt ht)]
      have htarget : projectedHeatDuhamelLagIntegrand (ν := ν) hc F t₀ ρ = 0 := by
        simp [projectedHeatDuhamelLagIntegrand, not_lt.mpr htρ.le]
      rw [htarget]
      have hEq' : (fun _ : ℝ => (0 : VectorH3 c)) =ᶠ[l]
          (fun t => projectedHeatDuhamelLagIntegrand (ν := ν) hc F t ρ) :=
        hEq.mono fun _ h => h.symm
      exact tendsto_const_nhds.congr' hEq'
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := H) (hF_meas := Filter.Eventually.of_forall hmeas)
    (h_bound := Filter.Eventually.of_forall hbound)
    (bound_integrable := hHInt) (h_lim := hlim)
  have hIntegral_eq {t : ℝ} (ht : t ∈ Icc 0 T) (htpos : 0 < t) :
      projectedHeatDuhamelIntegral (ν := ν) hc F t =
        ∫ ρ, projectedHeatDuhamelLagIntegrand (ν := ν) hc F t ρ ∂μ := by
    rw [projectedHeatDuhamelIntegral_eq_lag hc htpos F]
    change (∫ ρ in Ioo 0 t,
        projectedHeatDuhamelLagField (ν := ν) hc F t ρ) =
      ∫ ρ, (Ioo 0 t).indicator
        (projectedHeatDuhamelLagField (ν := ν) hc F t) ρ ∂μ
    rw [integral_indicator measurableSet_Ioo]
    have hrestrict : μ.restrict (Ioo 0 t) = volume.restrict (Ioo 0 t) := by
      dsimp [μ]
      rw [Measure.restrict_restrict measurableSet_Ioo]
      congr 1
      ext ρ
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨hρt, _⟩
        exact hρt
      · intro hρt
        exact ⟨hρt, ⟨hρt.1, lt_of_lt_of_le hρt.2 ht.2⟩⟩
    rw [hrestrict]
  have hdomain : ∀ᶠ t in l, t ∈ Icc 0 T := self_mem_nhdsWithin
  have hpos : ∀ᶠ t in l, 0 < t := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht₀)] with t ht
    exact ht
  have hEq : ∀ᶠ t in l,
      projectedHeatDuhamelIntegral (ν := ν) hc F t =
        ∫ ρ, projectedHeatDuhamelLagIntegrand (ν := ν) hc F t ρ ∂μ := by
    filter_upwards [hdomain, hpos] with t htdomain htp
    exact hIntegral_eq htdomain htp
  have hEqFun : (fun t => projectedHeatDuhamelIntegral (ν := ν) hc F t) =ᶠ[l]
      fun t => ∫ ρ, projectedHeatDuhamelLagIntegrand (ν := ν) hc F t ρ ∂μ :=
    hEq
  have hEq₀ : projectedHeatDuhamelIntegral (ν := ν) hc F t₀ =
      ∫ ρ, projectedHeatDuhamelLagIntegrand (ν := ν) hc F t₀ ρ ∂μ :=
    hIntegral_eq ⟨le_of_lt ht₀, le_of_lt hT⟩ ht₀
  have hcontWithin : Tendsto
      (fun t => projectedHeatDuhamelIntegral (ν := ν) hc F t) l
      (𝓝 (projectedHeatDuhamelIntegral (ν := ν) hc F t₀)) := by
    rw [hEq₀]
    exact hDCT.congr' hEqFun.symm
  have hfilter : l = 𝓝 t₀ := by
    dsimp [l]
    exact nhdsWithin_eq_nhds.mpr (Icc_mem_nhds ht₀ hT)
  rw [hfilter] at hcontWithin
  exact hcontWithin

#print axioms UnforcedLeray.TrainB.continuousAt_projectedHeatDuhamelIntegral_pos

end UnforcedLeray.TrainB
