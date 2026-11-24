import UnforcedLeray.Short.PartIIIa.Sub.T18_2

/-!
# Part III-a, shared helper for the leaves of `T18/2/*` and `T18/3/*`: bounds for the gain `g`

`gainG γ ν s = exp (γ s / (1 + ν s))` (`Defs.lean`). For `ν > 0` and `s ≥ 0` the exponent lies in
`[-|γ|/ν, |γ|/ν]` (`s/(1+νs) ≤ 1/ν`), so `g` is bounded above and below on `[0, ∞)`:
`exp (-|γ|/ν) ≤ g ≤ exp (|γ|/ν)`. (Proved here, compiled; used by the weighted-norm comparison
leaves.)
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem gainG_exponent_abs_le {γ ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    |γ * s / (1 + ν * s)| ≤ |γ| / ν := by
  have h1 : 0 < 1 + ν * s := by positivity
  rw [abs_div, abs_of_pos h1, abs_mul, abs_of_nonneg hs, div_le_div_iff₀ h1 hν]
  nlinarith [abs_nonneg γ, mul_nonneg (abs_nonneg γ) hs,
    mul_nonneg (abs_nonneg γ) (mul_nonneg hν.le hs)]

/-- `exp (-|γ|/ν) ≤ g(s) ≤ exp (|γ|/ν)` for `ν > 0`, `s ≥ 0`. -/
theorem gainG_bounds {γ ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    Real.exp (-(|γ| / ν)) ≤ gainG γ ν s ∧ gainG γ ν s ≤ Real.exp (|γ| / ν) := by
  have h := gainG_exponent_abs_le (γ := γ) hν hs
  unfold gainG
  exact ⟨Real.exp_le_exp.2 (by linarith [(abs_le.1 h).1]),
    Real.exp_le_exp.2 (by linarith [(abs_le.1 h).2])⟩

end UnforcedLeray.Short.IIIa
