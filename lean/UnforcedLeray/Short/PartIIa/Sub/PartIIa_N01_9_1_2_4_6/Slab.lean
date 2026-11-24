import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

/-- Slab Tonelli: a measurable `g ≥ 0` with uniformly bounded cell slices has finite integral over
`Icc s₁ s₂ ×ˢ cell c`. -/
theorem slab_lintegral_lt_top (c s₁ s₂ : ℝ) (g : ℝ × (ℝ × ℝ) → ENNReal) (hg : Measurable g)
    (K : ENNReal) (hK : K ≠ ⊤)
    (hb : ∀ s ∈ Icc s₁ s₂, ∫⁻ x in UnforcedLeray.B0579.cell c, g (s, x) ≤ K) :
    ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c, g p < ⊤ := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hg.aemeasurable]
  calc ∫⁻ s in Icc s₁ s₂, ∫⁻ x in UnforcedLeray.B0579.cell c, g (s, x) ∂volume
      ≤ ∫⁻ s in Icc s₁ s₂, K ∂volume := by
        refine setLIntegral_mono' measurableSet_Icc (fun s hs => hb s hs)
    _ = K * volume (Icc s₁ s₂) := by simp
    _ < ⊤ := ENNReal.mul_lt_top hK.lt_top (by simp)
