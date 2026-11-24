import UnforcedLeray.Short.PartIIa.Calc.BaseJets

/-!
# Part II-a, task `PartII-a:R02/8/20`: mean remainder part

Source of record: `the November 2 reference manuscript`, lines 447-459
(`sct:expansion` remainder with `N = 0`, `p = ∞`). The remainder bound
`s^{-(b+3)/2}` of `LateMeanRemainder` is weaker than the target size `s^{-(1/2+b/2)}` for `s ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

theorem meanRemPart_of (h : LateIngredients) : MeanRemPart := by
  intro ℓ b ρ m hρ
  obtain ⟨C, M, ν₀, hν₀, H⟩ := h.remainder ρ 0 m b ℓ hρ
  refine ⟨max C 0, M, ν₀, hν₀, fun ν hν hνle tr htr x hx => ?_⟩
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have hb := H ν hν hνle tr htr x hx
  have hexp : x.2.2 ^ (-(((b : ℝ) + 2 * ((0 : ℕ) : ℝ) + 3) / 2)) ≤
      x.2.2 ^ (-(1 / 2 + (b : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp only [Nat.cast_zero]; linarith)
  have hpos : 0 ≤ x.2.2 ^ (-(((b : ℝ) + 2 * ((0 : ℕ) : ℝ) + 3) / 2)) :=
    Real.rpow_nonneg (by linarith) _
  have hC : polyConst C M ν (ν ^ (-ρ)) ≤ polyConst (max C 0) M ν (ν ^ (-ρ)) :=
    polyConst_mono hν hc (le_max_left C 0) (le_max_right C 0) le_rfl
  have hP : 0 ≤ polyConst (max C 0) M ν (ν ^ (-ρ)) := by
    unfold polyConst
    have hinv : 0 < ν⁻¹ := inv_pos.2 hν
    exact mul_nonneg (le_max_right C 0) (pow_nonneg (by linarith) _)
  exact le_trans hb (mul_le_mul hC hexp hpos hP)
