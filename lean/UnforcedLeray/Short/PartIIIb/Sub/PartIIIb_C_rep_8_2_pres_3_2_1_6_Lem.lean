import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6_Base

/-!
# Decomposition of `liftPDecay`: young and old age regions of the pointwise decay

Source `the November 2 reference manuscript`
lines 1202, 1213-1225 (`p_raw = (R/r)^2 p`, smooth through the axis, bounded train pressure),
2541-2552 (large radius `ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`; `ϱ<R`: all-age heat expansion, arbitrary axial
decay), 2697-2713.  `age R y = R²/ϱ²` (`s`), young range `s ≤ 1/ν`, old range `s > 1/ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `LiftPPointwiseAt` restricted to the points of `S`. -/
def LiftPPointwiseOn (L : ReturnLevel) (S : Set Space) : Prop :=
  ∀ τ : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, y ∉ axis → y ∈ S →
    |liftP L τ y| ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) ∧
    ‖physGrad (liftP L τ) y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ)

theorem liftPPointwiseAt_of_on (L : ReturnLevel)
    (h1 : LiftPPointwiseOn L {y | age L.ε⁻¹ y ≤ L.ν⁻¹})
    (h2 : LiftPPointwiseOn L {y | L.ν⁻¹ < age L.ε⁻¹ y}) : LiftPPointwiseAt L := by
  intro τ
  obtain ⟨C1, hC1, b1⟩ := h1 τ
  obtain ⟨C2, hC2, b2⟩ := h2 τ
  refine ⟨max C1 C2, le_max_of_le_left hC1, fun y hy => ?_⟩
  have hp : 0 ≤ (1 + ‖y‖) ^ (-2 : ℝ) := by positivity
  rcases le_or_gt (age L.ε⁻¹ y) L.ν⁻¹ with h | h
  · obtain ⟨a, b⟩ := b1 y hy h
    exact ⟨a.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp),
      b.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)⟩
  · obtain ⟨a, b⟩ := b2 y hy h
    exact ⟨a.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp),
      b.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)⟩

theorem liftPDecay_of_regions (D : SeqData)
    (h1 : ∀ᶠ n : ℕ in atTop, LiftPPointwiseOn (D.level n) {y | age (D.level n).ε⁻¹ y ≤ (D.level n).ν⁻¹})
    (h2 : ∀ᶠ n : ℕ in atTop, LiftPPointwiseOn (D.level n) {y | (D.level n).ν⁻¹ < age (D.level n).ε⁻¹ y}) :
    D.LiftPDecay :=
  liftPDecay_of_pointwise D (by
    filter_upwards [h1, h2] with n a b using liftPPointwiseAt_of_on _ a b)

end UnforcedLeray.Short.PartIIIb.Concrete
