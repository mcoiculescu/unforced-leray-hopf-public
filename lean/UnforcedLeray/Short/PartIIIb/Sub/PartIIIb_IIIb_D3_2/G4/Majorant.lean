import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4Org
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4

open Set MeasureTheory

/-- Source 4659-4661: uniform integrable majorant `t^{μ+3/2} e^{-bt}`. -/
theorem testedMajorant (b : ℝ) (hb : 0 < b) (m₁ m₂ : ℝ) (h1 : 0 ≤ m₁) : ∃ C : ℝ, ∀ μ ∈ Set.Icc m₁ m₂, ∫ t in Set.Ioi (0:ℝ), t ^ (μ + 3/2) * Real.exp (-b * t) ≤ C := by
  have hint : ∀ a : ℝ, -1 < a → IntegrableOn (fun t : ℝ => t ^ a * Real.exp (-b * t)) (Ioi 0) := by
    intro a ha
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a) (b := b) ha one_pos hb
    simpa using this
  refine ⟨(∫ t in Set.Ioi (0:ℝ), t ^ (m₁ + 3/2) * Real.exp (-b * t)) +
    ∫ t in Set.Ioi (0:ℝ), t ^ (m₂ + 3/2) * Real.exp (-b * t), ?_⟩
  intro μ hμ
  have h2 : 0 ≤ m₂ := h1.trans (hμ.1.trans hμ.2)
  have i1 := hint (m₁ + 3/2) (by linarith)
  have i2 := hint (m₂ + 3/2) (by linarith)
  rw [← integral_add i1 i2]
  refine integral_mono_of_nonneg ?_ (i1.add i2) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have he := (Real.exp_pos (-b * t)).le
    have hle : t ^ (μ + 3/2) ≤ t ^ (m₁ + 3/2) + t ^ (m₂ + 3/2) := by
      rcases le_total 1 t with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h (show μ + 3/2 ≤ m₂ + 3/2 by linarith [hμ.2])
        have := Real.rpow_nonneg ht.le (m₁ + 3/2)
        linarith
      · have := Real.rpow_le_rpow_of_exponent_ge ht h (show m₁ + 3/2 ≤ μ + 3/2 by linarith [hμ.1])
        have := Real.rpow_nonneg ht.le (m₂ + 3/2)
        linarith
    show _ ≤ t ^ (m₁ + 3/2) * Real.exp (-b * t) + t ^ (m₂ + 3/2) * Real.exp (-b * t)
    nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4
