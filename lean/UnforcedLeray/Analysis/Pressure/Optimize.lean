import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Balancing the near and far Newtonian-gradient estimates

These numerical identities select the actual splitting radius `A / D`.
The vanishing velocity/derivative cases are handled by the forcing lemmas;
no positive lower bound on either energy quantity is assumed globally.
-/
noncomputable section
namespace UnforcedLeray.PressureAnalysis

/-- The near-kernel contribution at the balancing radius. -/
theorem balanced_near {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    (A / D) ^ (4 / 5 : ℝ) * D ^ 2 =
      A ^ (4 / 5 : ℝ) * D ^ (6 / 5 : ℝ) := by
  rw [Real.div_rpow hA.le hD.le]
  have h : D ^ (6 / 5 : ℝ) * D ^ (4 / 5 : ℝ) = D ^ 2 := by
    rw [← Real.rpow_add hD]
    norm_num [Real.rpow_natCast]
  rw [← h]
  field_simp

/-- The far-kernel contribution at the same balancing radius. -/
theorem balanced_far {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    (A / D) ^ (-1 / 5 : ℝ) * (A * D) =
      A ^ (4 / 5 : ℝ) * D ^ (6 / 5 : ℝ) := by
  rw [Real.div_rpow hA.le hD.le]
  have hA' : A ^ (-1 / 5 : ℝ) * A = A ^ (4 / 5 : ℝ) := by
    calc
      _ = A ^ (-1 / 5 : ℝ) * A ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = A ^ ((-1 / 5 : ℝ) + 1) := (Real.rpow_add hA _ _).symm
      _ = _ := by norm_num
  have hD' : D / D ^ (-1 / 5 : ℝ) = D ^ (6 / 5 : ℝ) := by
    calc
      _ = D ^ (1 : ℝ) / D ^ (-1 / 5 : ℝ) := by rw [Real.rpow_one]
      _ = D ^ ((1 : ℝ) - (-1 / 5)) := (Real.rpow_sub hD _ _).symm
      _ = _ := by norm_num
  calc
    _ = (A ^ (-1 / 5 : ℝ) * A) * (D / D ^ (-1 / 5 : ℝ)) := by ring
    _ = _ := by rw [hA', hD']

/-- The concrete two-term splitting estimate has the energy-scale powers. -/
theorem balanced_sum {A D : ℝ} (hA : 0 < A) (hD : 0 < D) (Cnear Cfar : ℝ) :
    Cnear * (A / D) ^ (4 / 5 : ℝ) * D ^ 2 +
      Cfar * (A / D) ^ (-1 / 5 : ℝ) * (A * D) =
      (Cnear + Cfar) * A ^ (4 / 5 : ℝ) * D ^ (6 / 5 : ℝ) := by
  calc
    _ = Cnear * ((A / D) ^ (4 / 5 : ℝ) * D ^ 2) +
        Cfar * ((A / D) ^ (-1 / 5 : ℝ) * (A * D)) := by ring
    _ = _ := by rw [balanced_near hA hD, balanced_far hA hD]; ring

/-- Raising the pressure estimate to `5/3` gives exactly the energy exponents. -/
theorem pressure_energy_power {C A D : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    (C * A ^ (4 / 5 : ℝ) * D ^ (6 / 5 : ℝ)) ^ (5 / 3 : ℝ) =
      C ^ (5 / 3 : ℝ) * A ^ (4 / 3 : ℝ) * D ^ 2 := by
  rw [Real.mul_rpow (mul_nonneg hC (Real.rpow_nonneg hA _))
      (Real.rpow_nonneg hD _),
    Real.mul_rpow hC (Real.rpow_nonneg hA _),
    ← Real.rpow_mul hA, ← Real.rpow_mul hD]
  norm_num [Real.rpow_natCast]

end UnforcedLeray.PressureAnalysis
