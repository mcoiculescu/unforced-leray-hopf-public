import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Part III-b: shared notation (not a manuscript item)

Notation for the shorter proof `the November 2 reference manuscript`.
The source writes `P_ν` for "a fixed polynomial in `ν⁻¹`", uniformly in the parameters that are
declared fixed.  `LePoly x y` is the exact meaning of "`x(ν) ≤ P_ν y(ν)` for small `ν`"
(lines 3883-3890, 4000-4130, 5111-5707): one constant `C` and one integer exponent `k`,
for all `0 < ν ≤ ν₀`.  The gain function `g(s) = exp(γ s/(1+νs))` is lines 3873, 5115.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

/-- `x(ν) ≤ P_ν · y(ν)` for all small `ν > 0`, where `P_ν = C ν⁻ᵏ` is a fixed polynomial in
`ν⁻¹` (the manuscript's `P_ν`). -/
def LePoly (x y : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → x ν ≤ C * ν⁻¹ ^ k * y ν

/-- `x(ν) ≤ P_ν e^{-c/ν}` for small `ν`. -/
def ExpSmall (x : ℝ → ℝ) (c : ℝ) : Prop :=
  LePoly x (fun ν => Real.exp (-c / ν))

/-- The gain function `g(s) = exp(γ s / (1 + ν s))` (lines 3873, 5115). -/
def gainFn (γ ν s : ℝ) : ℝ := Real.exp (γ * s / (1 + ν * s))

theorem gainFn_pos (γ ν s : ℝ) : 0 < gainFn γ ν s := Real.exp_pos _

end UnforcedLeray.Short.PartIIIb
