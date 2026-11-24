import UnforcedLeray.Short.PartIIb.Sub.G4_2_3_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.SumInvSq

/-!
# Part II-b, item `PartII-b:G4/2/3/4/4`: `perC_harmonic_exact`

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

For `x₂ ≠ 0` the `c`-periodization of the harmonic kernel `(y₁ - i y₂)^{-2}` is the
periodized inverse-square sum `Σ_{n∈ℤ} (z + n c)^{-2}` with `z = x₁ - i x₂`, which by
`sumInvSqShift` (SP 2349-2352) equals `(π/c)² / sin²(π z / c)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex

namespace UnforcedLeray.Short.IIb

/-- **`perC_harmonic_exact`** (SP 2349-2358): the `c`-periodization of `(y₁ - i y₂)^{-2}`
equals `(π/c)² / sin²(π (x₁ - i x₂)/c)` off the axis `x₂ = 0`. -/
theorem perC_harmonic_exact (c : ℝ) (hc : 0 < c) (x : ℝ × ℝ) (hx : x.2 ≠ 0) : UnforcedLeray.Short.IIb.perC c (fun y : ℝ × ℝ => (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) x = ((Real.pi : ℂ) / c) ^ 2 / Complex.sin (Real.pi * ((x.1 : ℂ) - (x.2 : ℂ) * Complex.I) / c) ^ 2 := by
  set z : ℂ := (x.1 : ℂ) - (x.2 : ℂ) * Complex.I with hzdef
  have hz : ∀ n : ℤ, z + (n : ℂ) * (c : ℂ) ≠ 0 := by
    intro n h
    have him := congrArg Complex.im h
    simp [hzdef] at him
    apply hx
    linarith
  have hterm : ∀ k : ℤ, (((x.1 + (k : ℝ) * c : ℝ) : ℂ) - ((x.2 : ℝ) : ℂ) * Complex.I) ^ (-2 : ℤ)
      = ((z + (k : ℂ) * (c : ℂ)) ^ 2)⁻¹ := by
    intro k
    have e : (((x.1 + (k : ℝ) * c : ℝ) : ℂ) - ((x.2 : ℝ) : ℂ) * Complex.I)
        = z + (k : ℂ) * (c : ℂ) := by
      rw [hzdef]
      push_cast
      ring
    rw [e, zpow_neg, zpow_two, pow_two]
  have hsum := sumInvSqShift c z hc hz
  have hperC : UnforcedLeray.Short.IIb.perC c
      (fun y : ℝ × ℝ => (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) x
      = ∑' k : ℤ, ((z + (k : ℂ) * (c : ℂ)) ^ 2)⁻¹ := by
    unfold UnforcedLeray.Short.IIb.perC
    exact tsum_congr (fun k => hterm k)
  rw [hperC, hsum.tsum_eq]
  ring

end UnforcedLeray.Short.IIb
