import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1_2

/-!
# Part I, task `PartI:S11/1/1/2/2`: `SecGreenInner`

If `φ` vanishes on `(0,a]`, then `greenN n φ r = c rⁿ` on `(0,a)`.

For `ρ > a > r` one has `min r ρ / max r ρ = r / ρ`, and the integrand vanishes for `ρ ≤ a`, so
`greenN n φ r = -(2n)⁻¹ rⁿ ∫_{(0,∞)} ρ^{-n} φ(ρ) ρ dρ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

/-- **Leaf `PartI:S11/1/1/2/2`** (lines 841-889 of the shorter proof): if `φ` vanishes on `(0,a]`,
then `greenN n φ r = c rⁿ` on `(0,a)`. -/
theorem secGreenInner_proof : UnforcedLeray.Short.PartI.SecGreenInner := by
  intro n hn φ hφ a ha hφa
  refine ⟨-(((2 * n : ℝ)⁻¹ : ℝ) : ℂ) * ∫ ρ in Ioi (0 : ℝ), (((ρ ^ n)⁻¹ : ℝ) : ℂ) * φ ρ * ρ, ?_⟩
  intro r hr hra
  unfold Planar.greenN
  have hpt : ∀ ρ ∈ Ioi (0 : ℝ),
      (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * φ ρ * ρ =
        (r : ℂ) ^ n * ((((ρ ^ n)⁻¹ : ℝ) : ℂ) * φ ρ * ρ) := by
    intro ρ _
    by_cases h : ρ ≤ a
    · simp [hφa ρ h]
    · push_neg at h
      have hmin : min r ρ = r := min_eq_left (by linarith)
      have hmax : max r ρ = ρ := max_eq_right (by linarith)
      rw [hmin, hmax, div_pow]
      push_cast
      ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  ring
