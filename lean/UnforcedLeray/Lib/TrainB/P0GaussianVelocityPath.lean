import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelIntegrable
import UnforcedLeray.Lib.TrainB.TensorBridge

/-!
# The actual nonlinear H³ Duhamel path

The tensor input is the previously proved row-oriented H³ product `u ⊗ u`. Its continuous path
and uniform graph estimate feed directly into the actual projected Gaussian Bochner-integrability
theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.TrainB

/-- The uniform H³ graph bound for the actual row tensor. -/
theorem norm_tensorH3Bilinear_apply_le {c : ℝ} (hc1 : 1 ≤ c)
    (u v : VectorH3 c) :
    ‖tensorH3Bilinear hc1 u v‖ ≤ 1536 * ‖u‖ * ‖v‖ := by
  change ‖tensorH3ProductValue hc1 u v‖ ≤ 1536 * ‖u‖ * ‖v‖
  calc
    _ ≤ tensorH3ProductConstant * ‖u‖ * ‖v‖ := tensorH3ProductValue_norm_le hc1 u v
    _ ≤ 1536 * ‖u‖ * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (tensorH3ProductConstant_le_1536 (c := c))
          (norm_nonneg u)) (norm_nonneg v)

/-- The continuous H³ stress path given by the actual tensor product `u ⊗ u`. -/
def tensorH3StressPath {c : ℝ} (hc1 : 1 ≤ c)
    (u : ContinuousMap ℝ (VectorH3 c)) : ContinuousMap ℝ (TensorH3 c) where
  toFun r := tensorH3Bilinear hc1 (u r) (u r)
  continuous_toFun := by
    have happly : Continuous
        (fun p : (VectorH3 c →L[ℝ] TensorH3 c) × VectorH3 c => p.1 p.2) := by
      fun_prop
    have hfirst : Continuous
        (fun r : ℝ => tensorH3Bilinear hc1 (u r)) :=
      (tensorH3Bilinear hc1).continuous.comp u.continuous
    exact happly.comp (hfirst.prodMk u.continuous)

/-- The actual projected nonlinear Gaussian path is Bochner integrable on every finite open
interval before the target time, for a continuous velocity path that is uniformly bounded in H³.
-/
theorem integrableOn_projectedHeatNonlinearity {c ν a s R : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (has : a < s) (hc1 : 1 ≤ c)
    (u : ContinuousMap ℝ (VectorH3 c))
    (hbound : ∀ r ∈ Set.Ioo a s, ‖u r‖ ≤ R) :
    Integrable
      (projectedHeatDuhamelOrbit (ν := ν) (s := s) hc (tensorH3StressPath hc1 u))
      (MeasureTheory.volume.restrict (Set.Ioo a s)) := by
  have hR : 0 ≤ R := by
    have hmid : (a + s) / 2 ∈ Set.Ioo a s := by constructor <;> linarith
    exact le_trans (norm_nonneg (u ((a + s) / 2))) (hbound ((a + s) / 2) hmid)
  have hstressBound : ∀ r ∈ Set.Ioo a s,
      ‖tensorH3StressPath hc1 u r‖ ≤ 1536 * R ^ 2 := by
    intro r hr
    change ‖tensorH3Bilinear hc1 (u r) (u r)‖ ≤ 1536 * R ^ 2
    calc
      _ ≤ 1536 * ‖u r‖ * ‖u r‖ := norm_tensorH3Bilinear_apply_le hc1 _ _
      _ ≤ 1536 * R ^ 2 := by
        have hsq : ‖u r‖ ^ 2 ≤ R ^ 2 :=
          (sq_le_sq₀ (norm_nonneg (u r)) hR).2 (hbound r hr)
        calc
          1536 * ‖u r‖ * ‖u r‖ = 1536 * ‖u r‖ ^ 2 := by ring
          _ ≤ 1536 * R ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
  exact integrableOn_projectedHeatDuhamelOrbit hc hν has
    (tensorH3StressPath hc1 u) hstressBound

#print axioms UnforcedLeray.TrainB.norm_tensorH3Bilinear_apply_le
#print axioms UnforcedLeray.TrainB.integrableOn_projectedHeatNonlinearity

end UnforcedLeray.TrainB
