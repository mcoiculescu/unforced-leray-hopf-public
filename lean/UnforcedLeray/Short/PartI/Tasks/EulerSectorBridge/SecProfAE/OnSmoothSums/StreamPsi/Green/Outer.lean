import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1_2

/-!
# Part I, task `PartI:S11/1/1/2/3`: `SecGreenOuter`

If `φ` vanishes on `[b,∞)`, then `greenN n φ r = c' r^{-n}` for `r > b`.

For `ρ < b < r` one has `min r ρ / max r ρ = ρ / r`, and the integrand vanishes for `ρ ≥ b`, so
`greenN n φ r = -(2n)⁻¹ r^{-n} ∫_{(0,∞)} ρⁿ φ(ρ) ρ dρ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

/-- **Leaf `PartI:S11/1/1/2/3`** (lines 841-889 of the shorter proof): if `φ` vanishes on `[b,∞)`,
then `greenN n φ r = c' r^{-n}` for `r > b`. -/
theorem secGreenOuter_proof : UnforcedLeray.Short.PartI.SecGreenOuter := by
  intro n hn φ hφ b hφb
  refine ⟨-(((2 * n : ℝ)⁻¹ : ℝ) : ℂ) * ∫ ρ in Ioi (0 : ℝ), ((ρ ^ n : ℝ) : ℂ) * φ ρ * ρ, ?_⟩
  intro r hr
  unfold Planar.greenN
  have hpt : ∀ ρ ∈ Ioi (0 : ℝ),
      (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * φ ρ * ρ =
        ((ρ ^ n : ℝ) : ℂ) * φ ρ * ρ * ((r : ℂ) ^ n)⁻¹ := by
    intro ρ _
    by_cases h : b ≤ ρ
    · simp [hφb ρ h]
    · push_neg at h
      have hmin : min r ρ = ρ := min_eq_right (by linarith)
      have hmax : max r ρ = r := max_eq_left (by linarith)
      rw [hmin, hmax, div_pow]
      push_cast
      ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_mul_const]
  ring
