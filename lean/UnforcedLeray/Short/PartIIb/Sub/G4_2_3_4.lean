import UnforcedLeray.Short.PartIIb.Sub.G4_2_3

/-!
# Part II-b, item `PartII-b:G4/2/3/4` (`PerHarmonicCut`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

`Hc` equals `M h`, `h(y) = (y₁ - i y₂)^{-2}`, for `|y| > ρ`.  Three leaves:

* `HcDerivDecay`: every derivative of `Hc` is `O((1+|y₁|)^{-2})` (outside the ball from the
  bound `|∂^j h| ≤ A_j |y|^{-2-j}`, inside by compactness).
* `PerSmoothSum`: such a function has a summable, smooth periodization (`contDiff_tsum`) whose
  derivatives are bounded uniformly in `c ≥ 1`.
* `PerHarmonicFar`: for `|x₂| ≥ 2ρ`, exponential decay from `sumInvSqShift` (SP 2349-2352) and
  Cauchy estimates for `csc²`.

Proved here: `perHarmonicCut_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- Leaf: all derivatives of the cut harmonic part decay like `(1+|y₁|)^{-2}` (SP 2349-2358). -/
def HcDerivDecay : Prop :=
  ∀ (Hc : ℝ × ℝ → ℂ) (ρ : ℝ) (M : ℂ), ContDiff ℝ ∞ Hc → 0 < ρ →
    (∀ y : ℝ × ℝ, ρ ^ 2 < y.1 ^ 2 + y.2 ^ 2 →
      Hc y = M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) →
    ∀ j : ℕ, ∃ B : ℝ, ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j Hc y‖ ≤ B / (1 + |y.1|) ^ 2

/-- Leaf: periodizing a smooth function with `(1+|y₁|)^{-2}` derivative decay (termwise
differentiation, `contDiff_tsum`); derivatives of the periodization are bounded uniformly in
`c ≥ 1`, since the nodes `x₁ + kc` are `1`-separated. -/
def PerSmoothSum : Prop :=
  ∀ (G : ℝ × ℝ → ℂ), ContDiff ℝ ∞ G →
    (∀ j : ℕ, ∃ B : ℝ, ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j G y‖ ≤ B / (1 + |y.1|) ^ 2) →
    (∀ c : ℝ, 1 ≤ c → (∀ x : ℝ × ℝ, Summable (fun k : ℤ => G (x.1 + k * c, x.2))) ∧
      ContDiff ℝ ∞ (perC c G)) ∧
    ∀ j : ℕ, ∃ B : ℝ, ∀ c : ℝ, 1 ≤ c → ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ j (perC c G) x‖ ≤ B

/-- Leaf: exponential decay of the periodized derivatives for `|x₂| ≥ 2ρ`, using
`perC c Hc = M (π/c)² csc²(π(x₁ - i x₂)/c)` there (`sumInvSqShift`), the bound
`|csc w|² ≤ 4 e^{-2|Im w|}/(1 - e^{-2|Im w|})²`, and Cauchy estimates on discs of radius `ρ`. -/
def PerHarmonicFar : Prop :=
  ∀ (Hc : ℝ × ℝ → ℂ) (ρ : ℝ) (M : ℂ), ContDiff ℝ ∞ Hc → 0 < ρ →
    (∀ y : ℝ × ℝ, ρ ^ 2 < y.1 ^ 2 + y.2 ^ 2 →
      Hc y = M * (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) ^ (-2 : ℤ))) →
    ∀ j : ℕ, ∃ (C κ : ℝ) (N : ℕ), 0 < C ∧ 0 < κ ∧ ∀ c : ℝ, 1 ≤ c → ∀ x : ℝ × ℝ,
      2 * ρ ≤ |x.2| →
        ‖iteratedFDeriv ℝ j (perC c Hc) x‖ ≤ C * c ^ N * Real.exp (-(κ * |x.2| / c))

theorem perHarmonicCut_of (h1 : HcDerivDecay) (h2 : PerSmoothSum) (h3 : PerHarmonicFar) :
    PerHarmonicCut := by
  intro Hc ρ M hHc hρ hout j
  obtain ⟨hsc, hB⟩ := h2 Hc hHc (h1 Hc ρ M hHc hρ hout)
  obtain ⟨B, hB'⟩ := hB j
  obtain ⟨C, κ, N, hC, hκ, hfar⟩ := h3 Hc ρ M hHc hρ hout j
  have hE : 0 < |B| * Real.exp (2 * ρ * κ) + C :=
    add_pos_of_nonneg_of_pos (by positivity) hC
  refine ⟨|B| * Real.exp (2 * ρ * κ) + C, κ, N, hE, hκ, fun c hc => ⟨(hsc c hc).1, (hsc c hc).2, ?_⟩⟩
  intro x
  have hc0 : 0 < c := by linarith
  have hcN : 1 ≤ c ^ N := one_le_pow₀ hc
  have hcN0 : 0 ≤ c ^ N := by positivity
  have hexp := Real.exp_pos (-(κ * |x.2| / c))
  by_cases hx : 2 * ρ ≤ |x.2|
  · calc _ ≤ C * c ^ N * Real.exp (-(κ * |x.2| / c)) := hfar c hc x hx
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hexp.le
        apply mul_le_mul_of_nonneg_right _ hcN0
        have : 0 ≤ |B| * Real.exp (2 * ρ * κ) := by positivity
        linarith
  · push Not at hx
    have h4 : ‖iteratedFDeriv ℝ j (perC c Hc) x‖ ≤ |B| := (hB' c hc x).trans (le_abs_self B)
    have hdiv : |x.2| / c ≤ 2 * ρ := by
      calc |x.2| / c ≤ |x.2| := div_le_self (abs_nonneg _) hc
        _ ≤ 2 * ρ := hx.le
    have hge : 1 ≤ Real.exp (2 * ρ * κ) * Real.exp (-(κ * |x.2| / c)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have : κ * |x.2| / c = κ * (|x.2| / c) := by ring
      rw [this]
      nlinarith
    calc ‖iteratedFDeriv ℝ j (perC c Hc) x‖ ≤ |B| := h4
      _ = |B| * 1 * 1 := by ring
      _ ≤ |B| * (Real.exp (2 * ρ * κ) * Real.exp (-(κ * |x.2| / c))) * c ^ N := by
        apply mul_le_mul _ hcN (by norm_num) (by positivity)
        calc |B| * 1 ≤ |B| * (Real.exp (2 * ρ * κ) * Real.exp (-(κ * |x.2| / c))) :=
          mul_le_mul_of_nonneg_left hge (abs_nonneg _)
          _ = _ := by ring
      _ ≤ (|B| * Real.exp (2 * ρ * κ) + C) * c ^ N * Real.exp (-(κ * |x.2| / c)) := by
        have : 0 ≤ C * c ^ N * Real.exp (-(κ * |x.2| / c)) := by positivity
        nlinarith [this]

end UnforcedLeray.Short.IIb
