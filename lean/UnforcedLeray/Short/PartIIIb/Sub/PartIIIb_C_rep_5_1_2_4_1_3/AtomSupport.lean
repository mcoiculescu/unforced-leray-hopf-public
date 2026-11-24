import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/13`: source ages across the radial gap

Source `the November 2 reference manuscript` 5586-5587 ("all source ages exceed
`e^{δ-h} s_j`").  If `y` has age `> s₁` and `ϱ z < θ ϱ y`, then `age z = R²/ϱ z² > s₁/θ²`, so the
kernel vanishes off the age window.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- **Source ages** (source 5586-5587): an atom across the radial gap from an output point of age
`> s₁` has age `> s₁/θ²`, so the kernel `phKer` vanishes at such atoms. -/
theorem atomSupport : AtomSupport := by
  intro R θ s1 s0 hR hθ hs1 τ y σ z hy hz hnot
  have hy' : s1 < age R y := by
    simp only [ybin, Set.mem_ofPred_eq, Set.mem_Ioc] at hy
    exact hy.1
  unfold phKer
  split_ifs with h
  · exfalso
    obtain ⟨-, hzy⟩ := h
    unfold age at hy' hnot
    have hϱ0 : 0 ≤ ϱ y := ϱ_nonneg y
    have hy2 : 0 < ϱ y ^ 2 := by
      by_contra hneg
      have h0 : ϱ y ^ 2 = 0 := le_antisymm (not_lt.1 hneg) (sq_nonneg _)
      rw [h0, div_zero] at hy'
      linarith
    have ha : 0 < ϱ y := by nlinarith
    have hθy : 0 < θ * ϱ y := mul_pos hθ ha
    have hb2 : ϱ z ^ 2 < (θ * ϱ y) ^ 2 := by
      nlinarith [mul_pos (sub_pos.2 hzy) (add_pos hz hθy)]
    have h3 : s1 * ϱ z ^ 2 < s1 * (θ * ϱ y) ^ 2 := mul_lt_mul_of_pos_left hb2 hs1
    have hsa : s1 * ϱ y ^ 2 < R ^ 2 := (lt_div_iff₀ hy2).1 hy'
    have h4 : θ ^ 2 * (s1 * ϱ y ^ 2) < θ ^ 2 * R ^ 2 :=
      mul_lt_mul_of_pos_left hsa (pow_pos hθ 2)
    have key : s1 * ϱ z ^ 2 < R ^ 2 * θ ^ 2 := by nlinarith [h3, h4]
    have hfrac : s1 / θ ^ 2 < R ^ 2 / ϱ z ^ 2 :=
      (div_lt_div_iff₀ (pow_pos hθ 2) (pow_pos hz 2)).2 key
    exact hnot hfrac
  · rfl

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
