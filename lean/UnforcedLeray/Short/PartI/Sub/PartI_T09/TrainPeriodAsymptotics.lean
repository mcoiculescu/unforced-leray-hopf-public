import UnforcedLeray.Short.PartI.Sub.PartI_T09

/-!
# Part I, task `PartI:T09/7`: `TrainPeriodAsymptotics`

Source of record: `the November 2 reference manuscript`, line 253
(`c = ν^{-ρ}`, `ρ > 1/2`, `e_c = (νc²)⁻¹ → 0`). Elementary: `ν c² = ν^{1-2ρ}`, and `1-2ρ < 0`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Leaf 5: the period** (`TrainPeriodAsymptotics`, `Sub/PartI_T09.lean`). -/
theorem trainPeriodAsymptotics_proof : TrainPeriodAsymptotics := by
  intro ρ hρ R hR
  have hα : 0 < 2 * ρ - 1 := by linarith
  have hne : (2 * ρ - 1) ≠ 0 := hα.ne'
  have htpos : 0 < R ^ (-(1 / (2 * ρ - 1))) := Real.rpow_pos_of_pos hR _
  have ht_eq : (R ^ (-(1 / (2 * ρ - 1)))) ^ (-(2 * ρ - 1)) = R := by
    rw [← Real.rpow_mul hR.le]
    have h : -(1 / (2 * ρ - 1)) * -(2 * ρ - 1) = 1 := by
      rw [neg_mul_neg, one_div, inv_mul_cancel₀ hne]
    rw [h, Real.rpow_one]
  refine ⟨min 1 (R ^ (-(1 / (2 * ρ - 1)))), lt_min one_pos htpos, min_le_left _ _, ?_⟩
  intro ν hν hνν
  have hν1 : ν ≤ 1 := le_trans hνν (min_le_left _ _)
  have hνt : ν ≤ R ^ (-(1 / (2 * ρ - 1))) := le_trans hνν (min_le_right _ _)
  refine ⟨?_, ?_⟩
  · unfold trainPeriod
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  · unfold trainPeriod
    have key : ν * (ν ^ (-ρ)) ^ 2 = ν ^ (-(2 * ρ - 1)) := by
      have h1 : ν * (ν ^ (-ρ)) ^ 2 = ν ^ (1 : ℝ) * (ν ^ (-ρ) * ν ^ (-ρ)) := by
        rw [Real.rpow_one, sq]
      rw [h1, ← Real.rpow_add hν, ← Real.rpow_add hν]
      congr 1
      ring
    rw [key]
    have h2 : (R ^ (-(1 / (2 * ρ - 1)))) ^ (-(2 * ρ - 1)) ≤ ν ^ (-(2 * ρ - 1)) :=
      Real.rpow_le_rpow_of_nonpos hν hνt (by linarith)
    rw [ht_eq] at h2
    exact h2

end UnforcedLeray.Short.PartI
