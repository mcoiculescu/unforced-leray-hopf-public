import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvThetaFacts
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvFluxFBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvErrDerivs

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/13`: `E_R` and its derivatives are `O(1/R)`

Target (`VtvFluxLemmas.lean`): `VtvErrBound`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

With `C` bounding `F` and `F'` (`VtvFluxFBound`) and `Cθ` bounding `θ'`, `θ''`, `θ'''`
(`VtvThetaFacts`), the explicit formulas of `VtvErrDerivs` give every component of `E_R`,
its age derivative, its gradient and its Laplacian as `F·θ^{(k)}(η/R)/R^k` (`k = 1,2,3`) or `0`.
Each is bounded by `C·Cθ/R` for `R ≥ 1`, using `R ≤ R²`, `R ≤ R³`.  Take `K = C·Cθ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Target: `VtvErrBound`. -/
theorem vtvErrBound : VtvErrBound := by
  intro c Φ s₁ s₂ R₀ hS
  obtain ⟨C, hC⟩ := vtvFluxFBound c Φ s₁ s₂ R₀ hS
  obtain ⟨-, -, -, -, Cθ, hCθ⟩ := vtvThetaFacts
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0).1
  have hCθ0 : 0 ≤ Cθ := le_trans (abs_nonneg _) (hCθ 0).1
  have hK : 0 ≤ C * Cθ := mul_nonneg hC0 hCθ0
  refine ⟨C * Cθ, fun R hR s x i => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hR1 : R ≤ R ^ 2 := by nlinarith
  have hR2 : R ≤ R ^ 3 := by nlinarith
  have hPK : ∀ a b : ℝ, |a| ≤ C → |b| ≤ Cθ → |a| * |b| ≤ C * Cθ := fun a b ha hb =>
    mul_le_mul ha hb (abs_nonneg _) hC0
  have hq1 : ∀ a b : ℝ, |a| ≤ C → |b| ≤ Cθ → |a * b / R| ≤ C * Cθ / R := by
    intro a b ha hb
    rw [abs_div, abs_mul, abs_of_pos hR0]
    exact div_le_div_of_nonneg_right (hPK a b ha hb) hR0.le
  have hq2 : ∀ a b : ℝ, |a| ≤ C → |b| ≤ Cθ → |a * b / R ^ 2| ≤ C * Cθ / R := by
    intro a b ha hb
    rw [abs_div, abs_mul, abs_of_pos (pow_pos hR0 2), div_le_div_iff₀ (pow_pos hR0 2) hR0]
    have h1 := mul_le_mul_of_nonneg_right (hPK a b ha hb) hR0.le
    have h2 := mul_le_mul_of_nonneg_left hR1 hK
    nlinarith
  have hq3 : ∀ a b : ℝ, |a| ≤ C → |b| ≤ Cθ → |a * b / R ^ 3| ≤ C * Cθ / R := by
    intro a b ha hb
    rw [abs_div, abs_mul, abs_of_pos (pow_pos hR0 3), div_le_div_iff₀ (pow_pos hR0 3) hR0]
    have h1 := mul_le_mul_of_nonneg_right (hPK a b ha hb) hR0.le
    have h2 := mul_le_mul_of_nonneg_left hR2 hK
    nlinarith
  have hpos0 : 0 ≤ C * Cθ / R := div_nonneg hK hR0.le
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := vtvErrDerivs c Φ s₁ s₂ R₀ hS R hR0.ne' s x
  have e0 : vtvErr Φ R₀ R s x 0 = vtvFluxF Φ R₀ s * deriv vtvTheta (x.2 / R) / R := by
    unfold vtvErr
    rw [if_pos rfl]
  have e1 : vtvErr Φ R₀ R s x 1 = 0 := by
    unfold vtvErr
    rw [if_neg (by decide)]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e0]
      exact hq1 _ _ (hC s).1 (hCθ _).1
    · rw [d1]
      exact hq1 _ _ (hC s).2 (hCθ _).1
    · rw [d4]
      exact hq3 _ _ (hC s).1 (hCθ _).2.2
    · intro j
      obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      · rw [d2, abs_zero]
        exact hpos0
      · rw [d3]
        exact hq2 _ _ (hC s).1 (hCθ _).2.1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1, abs_zero]
      exact hpos0
    · rw [d5, abs_zero]
      exact hpos0
    · rw [d7, abs_zero]
      exact hpos0
    · intro j
      rw [d6 j, abs_zero]
      exact hpos0

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
