import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelEstimate

/-!
# Uniform input bound for the actual projected H³ Duhamel integral

This is the linear-in-the-stress estimate needed to bound differences of two nonlinear Picard
iterates. The integrand remains the actual projected Gaussian heat-divergence response.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

/-- The actual projected Gaussian Duhamel integral for a continuous tensor path. -/
def projectedHeatDuhamelIntegral {c ν : ℝ} (hc : 0 < c)
    (F : ContinuousMap ℝ (TensorH3 c)) (t : ℝ) : VectorH3 c :=
  ∫ r in Ioo 0 t, projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r

private theorem toReal_ofReal_trainHeatCoeff_generic {θ : ℝ} (hθ : 0 < θ) :
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

/-- The actual projected Gaussian Duhamel integral is bounded by the uniform H³ norm of its
continuous tensor input times the explicit square-root kernel mass. -/
theorem norm_projectedHeatDuhamelIntegral_le {c ν t M : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (ht : 0 < t)
    (F : ContinuousMap ℝ (TensorH3 c))
    (hbound : ∀ r ∈ Ioo 0 t, ‖F r‖ ≤ M) :
    ‖projectedHeatDuhamelIntegral (ν := ν) hc F t‖ ≤
      (M * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
        ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ)) := by
  let f : ℝ → VectorH3 c :=
    projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F
  let K : ℝ := ‖(UnforcedLeray.Train.toVecL :
    UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM : 0 ≤ M := by
    have hmid : t / 2 ∈ Ioo (0 : ℝ) t := by constructor <;> linarith
    exact le_trans (norm_nonneg (F (t / 2))) (hbound (t / 2) hmid)
  have hInt : Integrable f (volume.restrict (Ioo 0 t)) :=
    integrableOn_projectedHeatDuhamelOrbit hc hν (by linarith) F hbound
  have hNormInt : Integrable (fun r => ‖f r‖) (volume.restrict (Ioo 0 t)) := hInt.norm
  have hCoeffInt := integrable_heatDivL2Coeff_Ioo hν ht
  have hMajorInt : Integrable
      (fun r : ℝ => (M * K) * heatDivL2Coeff (ν * (t - r)))
      (volume.restrict (Ioo 0 t)) := by
    simpa [K] using hCoeffInt.const_mul (M * K)
  have hpoint : ∀ r ∈ Ioo 0 t,
      ‖f r‖ ≤ (M * K) * heatDivL2Coeff (ν * (t - r)) := by
    intro r hr
    have hθ : 0 < ν * (t - r) := mul_pos hν (sub_pos.mpr hr.2)
    have hcoeffPos : 0 ≤ heatDivL2Coeff (ν * (t - r)) := by
      unfold heatDivL2Coeff
      positivity
    have hreal := toReal_ofReal_trainHeatCoeff_generic hθ
    have hheat := norm_actualHeatDivH3_le hc hθ (F r)
    have hcontract : ‖f r‖ ≤ ‖actualHeatDivH3Orbit hc (F r) (ν * (t - r))‖ := by
      change ‖P0H3CLM hc (actualHeatDivH3Orbit hc (F r) (ν * (t - r)))‖ ≤ _
      exact P0H3CLM_apply_norm_le hc _
    have hactual : actualHeatDivH3Orbit hc (F r) (ν * (t - r)) =
        actualHeatDivH3CLM hc hθ (F r) := by
      simp [actualHeatDivH3Orbit, hθ]
    have hscaled : ‖actualHeatDivH3CLM hc hθ (F r)‖ ≤
        (K * heatDivL2Coeff (ν * (t - r))) * ‖F r‖ := by
      rw [hreal] at hheat
      simpa [K, mul_assoc] using hheat
    calc
      ‖f r‖ ≤ ‖actualHeatDivH3Orbit hc (F r) (ν * (t - r))‖ := hcontract
      _ = ‖actualHeatDivH3CLM hc hθ (F r)‖ := by rw [hactual]
      _ ≤ (K * heatDivL2Coeff (ν * (t - r))) * ‖F r‖ := hscaled
      _ ≤ (K * heatDivL2Coeff (ν * (t - r))) * M :=
        mul_le_mul_of_nonneg_left (hbound r hr) (mul_nonneg hK hcoeffPos)
      _ = (M * K) * heatDivL2Coeff (ν * (t - r)) := by ring
  have hIntegralMono :
      ∫ r in Ioo 0 t, ‖f r‖ ≤
        ∫ r in Ioo 0 t, (M * K) * heatDivL2Coeff (ν * (t - r)) :=
    setIntegral_mono_on (hf := hNormInt) (hg := hMajorInt) measurableSet_Ioo hpoint
  calc
    ‖projectedHeatDuhamelIntegral (ν := ν) hc F t‖ ≤ ∫ r in Ioo 0 t, ‖f r‖ := by
      change ‖∫ r in Ioo 0 t, f r‖ ≤ _
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioo 0 t, (M * K) * heatDivL2Coeff (ν * (t - r)) := hIntegralMono
    _ = (M * K) * ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ)) := by
      rw [integral_const_mul, integral_heatDivL2Coeff_Ioo hν ht]
      simp

#print axioms UnforcedLeray.TrainB.norm_projectedHeatDuhamelIntegral_le

end UnforcedLeray.TrainB
