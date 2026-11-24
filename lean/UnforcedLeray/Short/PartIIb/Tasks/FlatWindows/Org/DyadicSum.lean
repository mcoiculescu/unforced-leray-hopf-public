import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DyadicSum.Helpers

/-!
Leaf `PartII-b:T13/1/9` (SP 1930-1931): finite overlap of the dyadic windows gives the global bound.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

theorem dyadicSummation : DyadicSummation := by
  intro r c hr hc f g₁ g₂ m K hm hK hf hg₁ hg₂ hyp
  have hr0 : 0 < r := by linarith
  have hA : ∀ k : ℤ, ENNReal.ofReal m * hNormOn c r (winOpen ((2 : ℝ) ^ k)) f ≤
      ENNReal.ofReal K * hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g₁ +
        ENNReal.ofReal K * hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g₂ := fun k => by
    rw [← mul_add]
    exact hyp k
  have hb1 := dys_W2 hr g₁ hg₁
  have hb2 := dys_W2 hr g₂ hg₂
  calc ENNReal.ofReal m * hNorm c r f
      = (∑' k : ℤ, (ENNReal.ofReal m * hNormOn c r (winOpen ((2 : ℝ) ^ k)) f) ^ r) ^ (1 / r) := by
        rw [dys_scale hr0, dys_norm_eq hr]
    _ ≤ (∑' k : ℤ, (ENNReal.ofReal K * hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g₁) ^ r) ^ (1 / r) +
          (∑' k : ℤ, (ENNReal.ofReal K * hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g₂) ^ r) ^ (1 / r) :=
        dys_mink hr _ _ _ hA
    _ = ENNReal.ofReal K * (∑' k : ℤ, hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g₁ ^ r) ^ (1 / r) +
          ENNReal.ofReal K * (∑' k : ℤ, hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g₂ ^ r) ^ (1 / r) := by
        rw [dys_scale hr0, dys_scale hr0]
    _ ≤ ENNReal.ofReal K * (4 * hNorm c r g₁) + ENNReal.ofReal K * (4 * hNorm c r g₂) :=
        by
          have e1 := dys_bound_one (B := fun k : ℤ => hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g₁) hr
            (hNorm c r g₁) hb1
          have e2 := dys_bound_one (B := fun k : ℤ => hNormOn c r (winSet2 ((2 : ℝ) ^ k)) g₂) hr
            (hNorm c r g₂) hb2
          gcongr
    _ = ENNReal.ofReal (4 * K) * (hNorm c r g₁ + hNorm c r g₂) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
        ring

end UnforcedLeray.Short.IIb
