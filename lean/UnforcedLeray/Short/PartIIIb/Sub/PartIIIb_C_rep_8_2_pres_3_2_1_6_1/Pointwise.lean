import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6_1.Train

/-!
# The pointwise decay of `p_lift` on the whole space, from `sct:fluctuation`

Source `the November 2 reference manuscript`
lines 439-446 (`sct:fluctuation`, Part I: the train pressure and its derivatives decay like
`e^{-κνs/c²}` at every age, with the transverse weight), 1213-1225, 2541-2552, 2697-2713.
`lpt_train_bounds` (Part I input `PartI.TrainFluctuationDecay`) and `lpc_core` give, for each level
with small `ν`, `|p_lift|, |∇p_lift| ≤ C (1+|y|)^{-2}` off the axis at every phase, in the young
range `s ≤ 1/ν` and the old range `s > 1/ν` alike.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem lpp_rpow_form {X C F : ℝ} (hX : 0 < X) (h : (X ^ 2) * F ≤ C) :
    F ≤ C * X ^ (-2 : ℝ) := by
  rw [Real.rpow_neg hX.le, Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

theorem lpp_level (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ L : ReturnLevel, L.ν ≤ ν₀ →
      LiftPPointwiseOn L (Set.univ : Set Space) := by
  obtain ⟨ν₀, hν₀, h⟩ := lpt_train_bounds hF
  refine ⟨ν₀, hν₀, fun L hL τ => ?_⟩
  obtain ⟨A, a, hA, ha, hdiff, hP, hG⟩ := h L.ν L.ν_pos hL L.train L.train_buc
  obtain ⟨C, hC, hy⟩ := lpc_core (R := L.ε⁻¹) (τ := τ) (inv_pos.2 L.ε_pos)
    (P := fun x : ℝ × (ℝ × ℝ) => L.train.p x.1 x.2) hdiff hA ha hP hG
  refine ⟨C, hC, fun y hyx _ => ?_⟩
  obtain ⟨h1, h2⟩ := hy y hyx
  have hX : 0 < 1 + ‖y‖ := by positivity
  exact ⟨lpp_rpow_form hX h1, lpp_rpow_form hX h2⟩

/-- Eventually along the sequence, the pointwise decay holds on every set. -/
theorem lpp_seq (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, LiftPPointwiseOn (D.level n) (Set.univ : Set Space) := by
  obtain ⟨ν₀, hν₀, h⟩ := lpp_level hF
  have ht := retNu_tendsto (Pl := D.Pl) D.σ₀ hst.omega_ne
  filter_upwards [ht.eventually (ge_mem_nhds hν₀)] with n hn
  exact h (D.level n) hn

theorem liftPPointwiseOn_mono {L : ReturnLevel} {S T : Set Space} (hST : T ⊆ S)
    (h : LiftPPointwiseOn L S) : LiftPPointwiseOn L T := by
  intro τ
  obtain ⟨C, hC, hb⟩ := h τ
  exact ⟨C, hC, fun y hy hyT => hb y hy (hST hyT)⟩

end UnforcedLeray.Short.PartIIIb.Concrete

end
