import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation.SliceFwdSpatial
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation.SliceShift

/-!
# Part II-a, task `PartII-a:F09/1/3/1/4`: `sliceFwdTaylor_all`

Source `the November 2 reference manuscript`, lines 1403-1413, 1426-1428.
Combines `sliceFwdSpatialTaylor` (task 1/3/1/1, at phase `t - s`) with `sliceShiftTaylor`
(task 1/3/1/2) applied to `Φ`, `L₀Φ` and `∂_τΦ`, through the algebraic identity
`S Φ(t-s) - Φ(t) + s L₀Φ(t) = [S Φ(t-s) - Φ(t-s) + s(L₀Φ - ∂_τΦ)(t-s)]
  + [Φ(t-s) - Φ(t) + s ∂_τΦ(t)] + s[L₀Φ(t) - L₀Φ(t-s)] + s[∂_τΦ(t-s) - ∂_τΦ(t)]`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Abstract four-term bookkeeping for the forward Taylor combination. -/
theorem sliceFwd_combine_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Sm pm p0 Lm L0' Dm D0 : E) (s a b c d : ℝ) (hs : 0 ≤ s)
    (hA : ‖Sm - pm + (s : ℂ) • (Lm - Dm)‖ ≤ a)
    (hB : ‖pm - p0 + (s : ℂ) • D0‖ ≤ b)
    (hC : ‖Lm - L0'‖ ≤ c * s) (hD : ‖Dm - D0‖ ≤ d * s) :
    ‖Sm - p0 + (s : ℂ) • L0'‖ ≤ a + b + c * s ^ 2 + d * s ^ 2 := by
  have key : Sm - p0 + (s : ℂ) • L0' =
      (Sm - pm + (s : ℂ) • (Lm - Dm)) + (pm - p0 + (s : ℂ) • D0) +
        (s : ℂ) • (L0' - Lm) + (s : ℂ) • (Dm - D0) := by
    module
  have hsn : ∀ X : E, ‖(s : ℂ) • X‖ = s * ‖X‖ := fun X => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs]
  have hX3 : ‖(s : ℂ) • (L0' - Lm)‖ ≤ c * s ^ 2 := by
    rw [hsn, norm_sub_rev]
    calc s * ‖Lm - L0'‖ ≤ s * (c * s) := mul_le_mul_of_nonneg_left hC hs
      _ = c * s ^ 2 := by ring
  have hX4 : ‖(s : ℂ) • (Dm - D0)‖ ≤ d * s ^ 2 := by
    rw [hsn]
    calc s * ‖Dm - D0‖ ≤ s * (d * s) := mul_le_mul_of_nonneg_left hD hs
      _ = d * s ^ 2 := by ring
  rw [key]
  calc ‖(Sm - pm + (s : ℂ) • (Lm - Dm)) + (pm - p0 + (s : ℂ) • D0) +
        (s : ℂ) • (L0' - Lm) + (s : ℂ) • (Dm - D0)‖
      ≤ ‖(Sm - pm + (s : ℂ) • (Lm - Dm)) + (pm - p0 + (s : ℂ) • D0) +
          (s : ℂ) • (L0' - Lm)‖ + ‖(s : ℂ) • (Dm - D0)‖ := norm_add_le _ _
    _ ≤ ‖(Sm - pm + (s : ℂ) • (Lm - Dm)) + (pm - p0 + (s : ℂ) • D0)‖ +
          ‖(s : ℂ) • (L0' - Lm)‖ + ‖(s : ℂ) • (Dm - D0)‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ‖Sm - pm + (s : ℂ) • (Lm - Dm)‖ + ‖pm - p0 + (s : ℂ) • D0‖ +
          ‖(s : ℂ) • (L0' - Lm)‖ + ‖(s : ℂ) • (Dm - D0)‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ a + b + c * s ^ 2 + d * s ^ 2 := by
          linarith

/-- **Forward slicewise Taylor bound, all phase tests** (task `PartII-a:F09/1/3/1/4`,
lines 1403-1413, 1426-1428). -/
theorem sliceFwdTaylor_all : SliceFwdTaylor := by
  intro p _ hp P _ ν hν Φ hΦ
  obtain ⟨C1, hC1, h1⟩ := sliceFwdSpatialTaylor p hp P ν hν Φ hΦ
  obtain ⟨C2, hC2, h2⟩ := sliceShiftTaylor p hp P Φ hΦ
  obtain ⟨C3, hC3, h3⟩ := sliceShiftTaylor p hp P (L0 ν Φ) (isPhaseTest_L0' hΦ ν)
  obtain ⟨C4, hC4, h4⟩ := sliceShiftTaylor p hp P (PhaseSpace.dτ Φ) hΦ.dτ
  refine ⟨C1 + C2 + C3 + C4, by linarith, fun t s hs0 hs1 => ?_⟩
  have hA := h1 (t - s) s hs0 hs1
  have hB := (h2 t s hs0 hs1).1
  have hC := (h3 t s hs0 hs1).2
  have hD := (h4 t s hs0 hs1).2
  have key := sliceFwd_combine_aux _ _ _ _ _ _ _ s (C1 * s ^ 2) (C2 * s ^ 2) C3 C4 hs0.le
    hA hB hC hD
  exact key.trans_eq (by ring)

end UnforcedLeray.Short.PartIIa
