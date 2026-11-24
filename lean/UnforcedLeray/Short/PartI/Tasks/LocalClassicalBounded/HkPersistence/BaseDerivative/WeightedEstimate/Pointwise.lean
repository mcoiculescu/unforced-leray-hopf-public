import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.BaseDerivative.WeightedEstimate.Kernel

/-!
# Pointwise Duhamel bound with an exponential weight (task `PartI:T02/1/2/4/1`)


the November 2 reference manuscript`, lines 261-288.

* `norm_projectedHeatDuhamelOrbit_le`: the integrand of the actual projected H³ Gaussian Duhamel
  integral is bounded by `‖toVecL‖ · heatDivL2Coeff(ν(t-r)) · ‖F r‖`.  The proof copies the
  integrand estimate of `norm_projectedHeatDuhamelIntegral_le`
  (`Lib/TrainB/P0GaussianDuhamelGenericBound.lean`).
* `norm_projectedHeatDuhamelIntegral_exp_le`: if `‖F r‖ ≤ M e^{λ r}` on `(0,t)`, then
  `‖∫_{(0,t)} ...‖ ≤ ‖toVecL‖ · M · (2 ν^{-1/2} / √λ) e^{λ t}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

namespace UnforcedLeray.Short.PartI.BilWE

private theorem toReal_ofReal_kernel {θ : ℝ} (hθ : 0 < θ) :
    (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
      ENNReal.ofReal (heatDivL2Coeff θ)).toReal =
      ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
        heatDivL2Coeff θ := by
  have hK : 0 ≤ ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ := norm_nonneg _
  have hcoeff : 0 ≤ heatDivL2Coeff θ := heatDivL2Coeff_nonneg' θ
  rw [← ENNReal.ofReal_mul hK]
  exact ENNReal.toReal_ofReal (mul_nonneg hK hcoeff)

/-- The integrand of the projected Gaussian Duhamel integral at age `t - r`. -/
theorem norm_projectedHeatDuhamelOrbit_le {c ν t : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (F : ℝ → TensorH3 c) (r : ℝ) (hr : r ∈ Ioo 0 t) :
    ‖projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r‖ ≤
      ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
        heatDivL2Coeff (ν * (t - r)) * ‖F r‖ := by
  have hθ : 0 < ν * (t - r) := mul_pos hν (sub_pos.mpr hr.2)
  have hreal := toReal_ofReal_kernel hθ
  have hheat := norm_actualHeatDivH3_le hc hθ (F r)
  have hcontract : ‖projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r‖ ≤
      ‖actualHeatDivH3Orbit hc (F r) (ν * (t - r))‖ := by
    change ‖P0H3CLM hc (actualHeatDivH3Orbit hc (F r) (ν * (t - r)))‖ ≤ _
    exact P0H3CLM_apply_norm_le hc _
  have hactual : actualHeatDivH3Orbit hc (F r) (ν * (t - r)) =
      actualHeatDivH3CLM hc hθ (F r) := by
    simp [actualHeatDivH3Orbit, hθ]
  have hscaled : ‖actualHeatDivH3CLM hc hθ (F r)‖ ≤
      (‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
        heatDivL2Coeff (ν * (t - r))) * ‖F r‖ := by
    rw [hreal] at hheat
    simpa [mul_assoc] using hheat
  calc ‖projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r‖
      ≤ ‖actualHeatDivH3Orbit hc (F r) (ν * (t - r))‖ := hcontract
    _ = ‖actualHeatDivH3CLM hc hθ (F r)‖ := by rw [hactual]
    _ ≤ _ := hscaled
    _ = _ := by ring

/-- The weighted Gaussian Duhamel bound: a weight `e^{λ r}` on the stress gives the weight
`e^{λ t}` on the Duhamel integral, with the constant `‖toVecL‖ · M · 2 ν^{-1/2} / √λ`. -/
theorem norm_projectedHeatDuhamelIntegral_exp_le {c ν t lam M : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hlam : 0 < lam) (ht : 0 ≤ t) (hM : 0 ≤ M) (F : ContinuousMap ℝ (TensorH3 c))
    (hbound : ∀ r ∈ Ioo 0 t, ‖F r‖ ≤ M * Real.exp (lam * r)) :
    ‖projectedHeatDuhamelIntegral (ν := ν) hc F t‖ ≤
      (‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ * M) *
        (2 * ν ^ (-(1 / 2 : ℝ)) / Real.sqrt lam * Real.exp (lam * t)) := by
  have hKnn : 0 ≤ ‖(UnforcedLeray.Train.toVecL :
      UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ := norm_nonneg _
  rcases ht.eq_or_lt with h0 | hpos
  · have hzero : projectedHeatDuhamelIntegral (ν := ν) hc F t = 0 := by
      rw [← h0]
      simp [projectedHeatDuhamelIntegral]
    rw [hzero, norm_zero]
    have hs : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
    have hν' : 0 < ν ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hν _
    have hA : 0 ≤ 2 * ν ^ (-(1 / 2 : ℝ)) / Real.sqrt lam * Real.exp (lam * t) := by
      positivity
    exact mul_nonneg (mul_nonneg hKnn hM) hA
  · unfold projectedHeatDuhamelIntegral
    have hexpmono : ∀ r ∈ Ioo 0 t, ‖F r‖ ≤ M * Real.exp (lam * t) := fun r hr =>
      (hbound r hr).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr.2.le hlam.le)) hM)
    have hint : Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F)
        (volume.restrict (Ioo 0 t)) :=
      integrableOn_projectedHeatDuhamelOrbit hc hν hpos F hexpmono
    have hNormInt : Integrable (fun r => ‖projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r‖)
        (volume.restrict (Ioo 0 t)) := hint.norm
    have hG : Integrable (fun r : ℝ => heatDivL2Coeff (ν * (t - r)) * Real.exp (lam * r))
        (volume.restrict (Ioo 0 t)) := by
      refine (integrable_heatDivL2Coeff_Ioo hν hpos).mul_bdd (c := Real.exp (lam * t)) ?_ ?_
      · exact (by fun_prop : Continuous fun r : ℝ => Real.exp (lam * r)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr.2.le hlam.le)
    have hpoint : ∀ r ∈ Ioo 0 t,
        ‖projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r‖ ≤
          (‖(UnforcedLeray.Train.toVecL :
            UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ * M) *
            (heatDivL2Coeff (ν * (t - r)) * Real.exp (lam * r)) := by
      intro r hr
      calc ‖projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r‖
          ≤ ‖(UnforcedLeray.Train.toVecL :
              UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
              heatDivL2Coeff (ν * (t - r)) * ‖F r‖ :=
            norm_projectedHeatDuhamelOrbit_le hc hν F r hr
        _ ≤ ‖(UnforcedLeray.Train.toVecL :
              UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
              heatDivL2Coeff (ν * (t - r)) * (M * Real.exp (lam * r)) :=
            mul_le_mul_of_nonneg_left (hbound r hr)
              (mul_nonneg hKnn (heatDivL2Coeff_nonneg' _))
        _ = _ := by ring
    calc ‖∫ r in Ioo 0 t, projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r‖
        ≤ ∫ r in Ioo 0 t, ‖projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ r in Ioo 0 t, (‖(UnforcedLeray.Train.toVecL :
            UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ * M) *
            (heatDivL2Coeff (ν * (t - r)) * Real.exp (lam * r)) :=
          setIntegral_mono_on hNormInt (hG.const_mul _) measurableSet_Ioo hpoint
      _ = (‖(UnforcedLeray.Train.toVecL :
            UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ * M) *
            ∫ r in Ioo 0 t, heatDivL2Coeff (ν * (t - r)) * Real.exp (lam * r) :=
          integral_const_mul _ _
      _ ≤ (‖(UnforcedLeray.Train.toVecL :
            UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ * M) *
            (2 * ν ^ (-(1 / 2 : ℝ)) / Real.sqrt lam * Real.exp (lam * t)) :=
          mul_le_mul_of_nonneg_left (heatDiv_exp_integral_le hν hlam ht) (mul_nonneg hKnn hM)

end UnforcedLeray.Short.PartI.BilWE
