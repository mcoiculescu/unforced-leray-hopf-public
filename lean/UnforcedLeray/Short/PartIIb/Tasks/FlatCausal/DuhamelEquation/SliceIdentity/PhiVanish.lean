import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_6

/-!
# Part II-b, task `PartII-b:T12/7/6/3` (`deqPhiVanish`): vanishing of `Φ_i` for large age

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
The test `Ψ` has compact support, so `Ψ(s,·) = 0` for `s` large, hence `deqSmooth ν Ψ i t s = 0`
and `∫ g_i deqSmooth_i = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/6/3`** (SP 1923-1927): `Φ_i(s) = 0` for `s ≥ H`. -/
theorem deqPhiVanish : UnforcedLeray.Short.IIb.DeqPhiVanish := by
  intro ν c r t hν ht hc hr g hg Ψ hΨ
  obtain ⟨C0, hC0⟩ := (hΨ.smooth 0).compact.isCompact.isBounded.exists_norm_le
  obtain ⟨C1, hC1⟩ := (hΨ.smooth 1).compact.isCompact.isBounded.exists_norm_le
  refine ⟨max C0 C1 + 1, fun s hs i => ?_⟩
  have hbd : ∀ w : ℝ × ℝ, Ψ (s, w) i = 0 := by
    intro w
    apply image_eq_zero_of_notMem_tsupport (f := fun x => Ψ x i)
    intro hmem
    have hnorm : ‖((s, w) : Coord)‖ ≤ max C0 C1 := by
      fin_cases i
      · exact (hC0 _ hmem).trans (le_max_left _ _)
      · exact (hC1 _ hmem).trans (le_max_right _ _)
    have h1 : ‖s‖ ≤ ‖((s, w) : Coord)‖ := norm_fst_le ((s, w) : Coord)
    rw [Real.norm_eq_abs] at h1
    have h2 := le_abs_self s
    linarith
  have hz : ∀ z : ℝ × ℝ, deqSmooth ν Ψ i t s z = 0 := fun z => by
    simp [deqSmooth, hbd]
  simp [hz]

end UnforcedLeray.Short.IIb
