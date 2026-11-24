import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Field.Periodic

/-!
# Uniform bound of a periodic continuous family on a strip (helper for the stream-test jets)

A continuous `Φ : ℝ × (ℝ × ℝ) → ℝ` which is `c`-periodic in the second slot's first
coordinate and vanishes for `|x.2| > R` is bounded on `[s₁,s₂] × ℝ²` by one constant.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem periodic_strip_bound {Φ : ℝ × (ℝ × ℝ) → ℝ} (hΦ : Continuous Φ) {c R : ℝ} (hc : 0 < c)
    (hper : ∀ s x, Φ (s, (x.1 + c, x.2)) = Φ (s, x))
    (hband : ∀ s x, R < |x.2| → Φ (s, x) = 0) (s₁ s₂ : ℝ) :
    ∃ K : ℝ, ∀ s ∈ Icc s₁ s₂, ∀ x : ℝ × ℝ, |Φ (s, x)| ≤ K := by
  have hK0 : IsCompact (Icc s₁ s₂ ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (E := ℝ) hK0 hΦ.continuousOn
  refine ⟨max C 0, fun s hs x => ?_⟩
  by_cases hx : R < |x.2|
  · rw [hband s x hx]
    simp
  · push Not at hx
    have hperx : Function.Periodic (fun t : ℝ => Φ (s, (t, x.2))) c := fun t => hper s (t, x.2)
    obtain ⟨y, hy, hxy⟩ := hperx.exists_mem_Ico₀ hc x.1
    have hyK : (s, (y, x.2)) ∈ Icc s₁ s₂ ×ˢ (Icc 0 c ×ˢ Icc (-R) R) :=
      ⟨hs, ⟨⟨hy.1, le_of_lt hy.2⟩, ⟨by linarith [neg_abs_le x.2], le_trans (le_abs_self _) hx⟩⟩⟩
    have hb := hC _ hyK
    have hxeq : Φ (s, x) = Φ (s, (y, x.2)) := hxy
    rw [hxeq]
    exact (hb.trans (le_max_left _ _))

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
