import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelPath
import UnforcedLeray.Lib.HeatCylinder.BochnerPath

/-!
# Bochner integrability of the actual projected H³ Duhamel path

For a continuous tensor path with a uniform H³ bound, the actual projected Gaussian response is
continuous on the open time interval and its norm is dominated by the integrable square-root
kernel. This supplies the Bochner integrability needed before defining the nonlinear Duhamel map.
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

/-- The actual projected Gaussian Duhamel path is Bochner integrable on every finite open time
interval before the target time, provided its tensor H³ input is continuous and uniformly bounded.
The norm majorant is the existing concrete Gaussian heat-divergence kernel coefficient. -/
theorem integrableOn_projectedHeatDuhamelOrbit {c ν a s M : ℝ} (hc : 0 < c)
    (hν : 0 < ν) (has : a < s)
    (F : ContinuousMap ℝ (TensorH3 c))
    (hbound : ∀ r ∈ Ioo a s, ‖F r‖ ≤ M) :
    Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := s) hc F)
      (volume.restrict (Ioo a s)) := by
  let f : ℝ → VectorH3 c := projectedHeatDuhamelOrbit (ν := ν) (s := s) hc F
  let K : ℝ := ‖(UnforcedLeray.Train.toVecL :
    UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcont : ContinuousOn f (Ioo a s) := by
    intro r hr
    exact (continuousAt_projectedHeatDuhamelOrbit hc hν hr.2
      F.continuous.continuousAt).continuousWithinAt
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioo a s)) :=
    hcont.aestronglyMeasurable_of_isSeparable measurableSet_Ioo
      (TopologicalSpace.IsSeparable.of_separableSpace (Ioo a s))
  have hcoeff := integrable_heatDivL2Coeff_Ioo hν has
  have hmajor : Integrable
      (fun r : ℝ => (M * K) * heatDivL2Coeff (ν * (s - r)))
      (volume.restrict (Ioo a s)) := by
    simpa using hcoeff.const_mul (M * K)
  refine hmajor.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hθ : 0 < ν * (s - r) := mul_pos hν (sub_pos.mpr hr.2)
  have hcoeffPos : 0 ≤ heatDivL2Coeff (ν * (s - r)) := by
    unfold heatDivL2Coeff
    positivity
  have hreal := toReal_ofReal_trainHeatCoeff hθ
  have hheat := norm_actualHeatDivH3_le hc hθ (F r)
  have hactual : actualHeatDivH3Orbit hc (F r) (ν * (s - r)) =
      actualHeatDivH3CLM hc hθ (F r) := by
    simp [actualHeatDivH3Orbit, hθ]
  calc
    ‖f r‖ ≤ ‖actualHeatDivH3Orbit hc (F r) (ν * (s - r))‖ := by
      change ‖P0H3CLM hc (actualHeatDivH3Orbit hc (F r) (ν * (s - r)))‖ ≤ _
      exact P0H3CLM_apply_norm_le hc _
    _ = ‖actualHeatDivH3CLM hc hθ (F r)‖ := by rw [hactual]
    _ ≤ K * heatDivL2Coeff (ν * (s - r)) * ‖F r‖ := by
      rw [hreal] at hheat
      simpa [K] using hheat
    _ ≤ K * heatDivL2Coeff (ν * (s - r)) * M := by
      exact mul_le_mul_of_nonneg_left (hbound r hr)
        (mul_nonneg hK hcoeffPos)
    _ = (M * K) * heatDivL2Coeff (ν * (s - r)) := by ring

#print axioms UnforcedLeray.TrainB.integrableOn_projectedHeatDuhamelOrbit

end UnforcedLeray.TrainB
