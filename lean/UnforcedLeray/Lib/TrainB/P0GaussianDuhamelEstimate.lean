import UnforcedLeray.Lib.TrainB.P0GaussianVelocityPath

/-!
# The actual H³ nonlinear Duhamel integral and its local-time bound

This leaf defines the set-integral of the actual projected Gaussian response of the actual row
tensor. Its norm is bounded by the explicit square-root kernel mass, with no unproved heat or
projection map.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

private theorem toReal_ofReal_trainHeatCoeff {θ : ℝ} (hθ : 0 < θ) :
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

/-- The actual projected nonlinear H³ Duhamel term at time `t`. -/
def projectedHeatNonlinearityIntegral {c ν : ℝ} (hc : 0 < c)
    (hc1 : 1 ≤ c) (u : ContinuousMap ℝ (VectorH3 c)) (t : ℝ) : VectorH3 c :=
  ∫ r in Ioo 0 t,
    projectedHeatDuhamelOrbit (ν := ν) (s := t) hc (tensorH3StressPath hc1 u) r

/-- Exact square-root-time norm bound for the actual projected nonlinear Duhamel term. -/
theorem norm_projectedHeatNonlinearityIntegral_le {c ν t R : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (ht : 0 < t) (hc1 : 1 ≤ c)
    (u : ContinuousMap ℝ (VectorH3 c))
    (hbound : ∀ r ∈ Ioo 0 t, ‖u r‖ ≤ R) :
    ‖projectedHeatNonlinearityIntegral (ν := ν) hc hc1 u t‖ ≤
      (1536 * R ^ 2 * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
        ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ)) := by
  let F : ContinuousMap ℝ (TensorH3 c) := tensorH3StressPath hc1 u
  let f : ℝ → VectorH3 c :=
    projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F
  let K : ℝ := ‖(UnforcedLeray.Train.toVecL :
    UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hFbound : ∀ r ∈ Ioo 0 t, ‖F r‖ ≤ 1536 * R ^ 2 := by
    intro r hr
    change ‖tensorH3Bilinear hc1 (u r) (u r)‖ ≤ 1536 * R ^ 2
    calc
      _ ≤ 1536 * ‖u r‖ * ‖u r‖ := norm_tensorH3Bilinear_apply_le hc1 _ _
      _ ≤ 1536 * R ^ 2 := by
        have hsq : ‖u r‖ ^ 2 ≤ R ^ 2 :=
          (sq_le_sq₀ (norm_nonneg (u r))
            (le_trans (norm_nonneg (u r)) (hbound r hr))).2 (hbound r hr)
        calc
          1536 * ‖u r‖ * ‖u r‖ = 1536 * ‖u r‖ ^ 2 := by ring
          _ ≤ 1536 * R ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hInt : Integrable f (volume.restrict (Ioo 0 t)) := by
    exact integrableOn_projectedHeatNonlinearity hc hν (by linarith) hc1 u hbound
  have hNormInt : Integrable (fun r => ‖f r‖) (volume.restrict (Ioo 0 t)) := hInt.norm
  have hCoeffInt := integrable_heatDivL2Coeff_Ioo hν (by linarith : (0 : ℝ) < t)
  have hMajorInt : Integrable
      (fun r : ℝ => (1536 * R ^ 2 * K) * heatDivL2Coeff (ν * (t - r)))
      (volume.restrict (Ioo 0 t)) := by
    simpa [K] using hCoeffInt.const_mul (1536 * R ^ 2 * K)
  have hpoint : ∀ r ∈ Ioo 0 t,
      ‖f r‖ ≤ (1536 * R ^ 2 * K) * heatDivL2Coeff (ν * (t - r)) := by
    intro r hr
    have hθ : 0 < ν * (t - r) := mul_pos hν (sub_pos.mpr hr.2)
    have hcoeffPos : 0 ≤ heatDivL2Coeff (ν * (t - r)) := by
      unfold heatDivL2Coeff
      positivity
    have hreal := toReal_ofReal_trainHeatCoeff hθ
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
      _ ≤ (K * heatDivL2Coeff (ν * (t - r))) * (1536 * R ^ 2) :=
        mul_le_mul_of_nonneg_left (hFbound r hr) (mul_nonneg hK hcoeffPos)
      _ = (1536 * R ^ 2 * K) * heatDivL2Coeff (ν * (t - r)) := by ring
  have hIntegralMono :
      ∫ r in Ioo 0 t, ‖f r‖ ≤
        ∫ r in Ioo 0 t, (1536 * R ^ 2 * K) * heatDivL2Coeff (ν * (t - r)) :=
    setIntegral_mono_on (hf := hNormInt) (hg := hMajorInt)
      measurableSet_Ioo hpoint
  calc
    ‖projectedHeatNonlinearityIntegral (ν := ν) hc hc1 u t‖ ≤
        ∫ r in Ioo 0 t, ‖f r‖ := by
          change ‖∫ r in Ioo 0 t, f r‖ ≤ _
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioo 0 t, (1536 * R ^ 2 * K) *
          heatDivL2Coeff (ν * (t - r)) := hIntegralMono
    _ = (1536 * R ^ 2 * K) *
          ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ)) := by
          rw [integral_const_mul, integral_heatDivL2Coeff_Ioo hν ht]
          simp

#print axioms UnforcedLeray.TrainB.projectedHeatNonlinearityIntegral
#print axioms UnforcedLeray.TrainB.norm_projectedHeatNonlinearityIntegral_le

end UnforcedLeray.TrainB
