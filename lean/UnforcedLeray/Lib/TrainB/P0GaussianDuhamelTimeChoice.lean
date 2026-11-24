import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelUniform

/-!
# Explicit short-time choice for the nonlinear contraction coefficient

The actual Duhamel Lipschitz estimate has a `√T` factor. This leaf gives a concrete positive time
on which that coefficient is at most one half.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.TrainB

/-- The explicit coefficient of the uniform trajectory distance in the nonlinear Duhamel bound. -/
def projectedHeatNonlinearityLipschitzCoeff (ν R : ℝ) : ℝ :=
  3072 * R * ‖(UnforcedLeray.Train.toVecL :
    UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ *
    (4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ))

/-- A positive time with an explicit half-contraction upper bound for the Gaussian nonlinearity. -/
theorem exists_train_short_contraction_time {ν R : ℝ} (hν : 0 < ν) (hR : 0 ≤ R) :
    ∃ T : ℝ, 0 < T ∧
      projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ) ≤ 1 / 2 := by
  let A : ℝ := projectedHeatNonlinearityLipschitzCoeff ν R
  have hA : 0 ≤ A := by
    dsimp [A, projectedHeatNonlinearityLipschitzCoeff]
    positivity
  let y : ℝ := 1 / (4 * (A + 1))
  have hy : 0 < y := by
    dsimp [y]
    positivity
  let T : ℝ := y ^ 2
  have hT : 0 < T := by dsimp [T]; positivity
  have hroot : T ^ (1 / 2 : ℝ) = y := by
    rw [show T = y ^ 2 by rfl, ← Real.sqrt_eq_rpow, Real.sqrt_sq hy.le]
  have hAy : A * y ≤ 1 / 4 := by
    dsimp [y]
    calc
      A * (1 / (4 * (A + 1))) = A / (4 * (A + 1)) := by ring
      _ ≤ 1 / 4 := (div_le_iff₀ (by positivity : 0 < 4 * (A + 1))).2 (by nlinarith)
  refine ⟨T, hT, ?_⟩
  rw [hroot]
  change A * y ≤ 1 / 2
  nlinarith [hAy]

#print axioms UnforcedLeray.TrainB.exists_train_short_contraction_time

end UnforcedLeray.TrainB
