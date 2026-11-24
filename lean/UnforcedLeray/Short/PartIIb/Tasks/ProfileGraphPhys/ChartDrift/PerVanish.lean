import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift

/-!
# `PartII-b:T10/6/3/1/1c`: the periodization is supported in a compact `s, η` box

Each term of the `ℤ`-sum has the same `s` and `η` as `x`, so it vanishes unless `x` lies in
the box containing `tsupport φ` in `(s, η)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.ChartLift

theorem perVanish_proof : UnforcedLeray.Short.IIb.ChartLift.PerVanish := by
  intro c φ _hc hφ
  have hcpt : IsCompact (tsupport φ) := hφ.compact
  have hbox : ∃ s₀ s₁ L : ℝ, 0 < s₀ ∧
      ∀ y : Coord, φ y ≠ 0 → s₀ ≤ y.1 ∧ y.1 ≤ s₁ ∧ |y.2.2| ≤ L := by
    rcases (tsupport φ).eq_empty_or_nonempty with hK | hK
    · refine ⟨1, 1, 1, one_pos, fun y hy => ?_⟩
      have h := subset_tsupport φ hy
      rw [hK] at h
      simp at h
    · obtain ⟨m, hm, hmin⟩ := hcpt.exists_isMinOn hK continuous_fst.continuousOn
      obtain ⟨m', hm', hmax⟩ := hcpt.exists_isMaxOn hK continuous_fst.continuousOn
      obtain ⟨n, hn, hnmax⟩ :=
        hcpt.exists_isMaxOn hK (continuous_abs.comp (continuous_snd.comp continuous_snd)).continuousOn
      refine ⟨m.1, m'.1, |n.2.2|, (hφ.supp hm).1, fun y hy => ⟨?_, ?_, ?_⟩⟩
      · exact isMinOn_iff.mp hmin y (subset_tsupport φ hy)
      · exact isMaxOn_iff.mp hmax y (subset_tsupport φ hy)
      · exact isMaxOn_iff.mp hnmax y (subset_tsupport φ hy)
  obtain ⟨s₀, s₁, L, hs₀, hb⟩ := hbox
  refine ⟨s₀, s₁, L, hs₀, fun x hx => ?_⟩
  have hz : ∀ k : ℤ, φ (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = 0 := by
    intro k
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hb _ h
    have e1 : s₀ ≤ x.1 := h1
    have e2 : x.1 ≤ s₁ := h2
    have e3 : |x.2.2| ≤ L := h3
    rcases hx with hx | hx | hx <;> linarith
  unfold perCoord
  simp only [hz, tsum_zero]

end UnforcedLeray.Short.IIb.ChartLift
