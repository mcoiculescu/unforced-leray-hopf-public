import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelAtZero

/-!
# Lag representation of the actual Gaussian Duhamel integral

Changing variables to the positive heat age fixes the singularity at the left endpoint and is the
basis for dominated convergence in the target time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set intervalIntegral

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

/-- The actual projected Gaussian response written in lag coordinates. -/
def projectedHeatDuhamelLagField {c ν : ℝ} (hc : 0 < c)
    (F : ContinuousMap ℝ (TensorH3 c)) (t ρ : ℝ) : VectorH3 c :=
  P0H3CLM hc (actualHeatDivH3Orbit hc (F (t - ρ)) (ν * ρ))

/-- The Duhamel integral equals the fixed-age lag integral after reversing time. -/
theorem projectedHeatDuhamelIntegral_eq_lag {c ν t : ℝ}
    (hc : 0 < c) (ht : 0 < t) (F : ContinuousMap ℝ (TensorH3 c)) :
    projectedHeatDuhamelIntegral (ν := ν) hc F t =
      ∫ ρ in Ioo 0 t, projectedHeatDuhamelLagField (ν := ν) hc F t ρ := by
  calc
    projectedHeatDuhamelIntegral (ν := ν) hc F t =
        ∫ r in (0 : ℝ)..t,
          projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r := by
      change ∫ r in Ioo 0 t,
          projectedHeatDuhamelOrbit (ν := ν) (s := t) hc F r = _
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le]
    _ = ∫ ρ in (0 : ℝ)..t, projectedHeatDuhamelLagField (ν := ν) hc F t ρ := by
      calc
        _ = ∫ r in (0 : ℝ)..t,
            projectedHeatDuhamelLagField (ν := ν) hc F t (t - r) := by
          refine intervalIntegral.integral_congr fun r _ => ?_
          simp [projectedHeatDuhamelOrbit, projectedHeatDuhamelLagField,
            sub_sub_cancel, sub_sub_cancel_left]
        _ = ∫ ρ in (0 : ℝ)..t, projectedHeatDuhamelLagField (ν := ν) hc F t ρ := by
          simpa [sub_self] using intervalIntegral.integral_comp_sub_left
            (fun ρ : ℝ => projectedHeatDuhamelLagField (ν := ν) hc F t ρ)
            (a := (0 : ℝ)) (b := t) t
    _ = ∫ ρ in Ioo 0 t, projectedHeatDuhamelLagField (ν := ν) hc F t ρ := by
      rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]

#print axioms UnforcedLeray.TrainB.projectedHeatDuhamelLagField
#print axioms UnforcedLeray.TrainB.projectedHeatDuhamelIntegral_eq_lag

end UnforcedLeray.TrainB
