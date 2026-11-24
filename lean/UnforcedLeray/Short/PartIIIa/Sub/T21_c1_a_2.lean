import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff

theorem seedGaussHalf_proof : UnforcedLeray.Short.IIIa.SeedGaussHalf := by
  unfold UnforcedLeray.Short.IIIa.SeedGaussHalf
  intro h hdec
  obtain ⟨C0, N, hC⟩ := hdec
  refine ⟨|C0| * Real.exp (2 * (N : ℝ) ^ 2), fun y => ?_⟩
  have hsq : ‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [UnforcedLeray.Short.IIIa.planeToC]
    ring
  have hs0 : 0 ≤ ‖UnforcedLeray.Short.IIIa.planeToC y‖ := norm_nonneg _
  have h1 := hC (UnforcedLeray.Short.IIIa.planeToC y)
  have h2 : (1 + ‖UnforcedLeray.Short.IIIa.planeToC y‖) ^ N ≤
      Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2 / 8) := by
    have a1 : (1 + ‖UnforcedLeray.Short.IIIa.planeToC y‖) ^ N ≤
        (Real.exp ‖UnforcedLeray.Short.IIIa.planeToC y‖) ^ N := by
      gcongr
      linarith [Real.add_one_le_exp ‖UnforcedLeray.Short.IIIa.planeToC y‖]
    rw [← Real.exp_nat_mul] at a1
    have a2 : (N : ℝ) * ‖UnforcedLeray.Short.IIIa.planeToC y‖ ≤
        ‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2 / 8 + 2 * (N : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (‖UnforcedLeray.Short.IIIa.planeToC y‖ - 4 * (N : ℝ))]
    have a3 := Real.exp_le_exp.mpr a2
    rw [Real.exp_add] at a3
    linarith [a1, a3]
  have hP : 0 ≤ (1 + ‖UnforcedLeray.Short.IIIa.planeToC y‖) ^ N := by positivity
  calc ‖UnforcedLeray.Short.PartI.seedPlanar h (UnforcedLeray.Short.IIIa.planeToC y)‖
      ≤ C0 * (1 + ‖UnforcedLeray.Short.IIIa.planeToC y‖) ^ N *
          Real.exp (-(‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2) / 4) := h1
    _ ≤ |C0| * (1 + ‖UnforcedLeray.Short.IIIa.planeToC y‖) ^ N *
          Real.exp (-(‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2) / 4) := by
      gcongr
      exact le_abs_self C0
    _ ≤ |C0| * (Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2 / 8)) *
          Real.exp (-(‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2) / 4) := by
      gcongr
    _ = |C0| * Real.exp (2 * (N : ℝ) ^ 2) *
          Real.exp (-(‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2) / 8) := by
      rw [show -(‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2) / 8 =
          ‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2 / 8 + (-(‖UnforcedLeray.Short.IIIa.planeToC y‖ ^ 2) / 4) by ring,
        Real.exp_add]
      ring
    _ = |C0| * Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
      rw [← hsq]
