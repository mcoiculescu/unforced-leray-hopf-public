import UnforcedLeray.Short.PartIIb.Sub.T12_7
import UnforcedLeray.Short.PartIIb.Sub.T12_7_7_2

/-!
# Helper for `PartII-b:T12/7/7/2/1` (`deqAbsSupport`): the transpose test is supported in a box

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

`deqTransposeTest` makes each component `flatTranspose ν μ Ψ · i` continuous with compact support
inside `{s > 0}`. Let `A` be the compact union of the two supports. Then `A` lies in a box
`[σ, R] × [-R, R]²` with `σ > 0` (the first coordinate is bounded below on `A` by its minimum, which is
positive), and the sum of norms is bounded on `A` and vanishes off `A`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T12/7/7/2/1`**: `∑_i ‖flatTranspose ν μ Ψ x i‖` is bounded by `K` and vanishes
outside a box `[σ,H] × [-R,R]²` with `σ > 0`. -/
theorem deqAbsSupport : UnforcedLeray.Short.IIb.DeqAbsSupport := by
  intro ν μ Ψ hΨ
  have h0 := deqTransposeTest ν μ hΨ 0
  have h1 := deqTransposeTest ν μ hΨ 1
  have hA : IsCompact (tsupport (fun x => flatTranspose ν μ Ψ x 0) ∪
      tsupport (fun x => flatTranspose ν μ Ψ x 1)) :=
    h0.2.1.isCompact.union h1.2.1.isCompact
  set A := tsupport (fun x => flatTranspose ν μ Ψ x 0) ∪
      tsupport (fun x => flatTranspose ν μ Ψ x 1) with hAdef
  have hAsub : A ⊆ Ioi (0 : ℝ) ×ˢ univ := Set.union_subset h0.2.2 h1.2.2
  -- the first coordinate is bounded below by a positive constant on `A`
  obtain ⟨σ, hσ, hσA⟩ : ∃ σ : ℝ, 0 < σ ∧ ∀ x ∈ A, σ ≤ x.1 := by
    by_cases hne : A.Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ := hA.exists_isMinOn hne continuous_fst.continuousOn
      exact ⟨x₀.1, (hAsub hx₀).1, fun x hx => isMinOn_iff.1 hmin x hx⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  -- a norm bound on `A`
  obtain ⟨R₀, hR₀⟩ := (hA.image continuous_norm).bddAbove
  have hnorm : ∀ x ∈ A, ‖x‖ ≤ R₀ := fun x hx => hR₀ (Set.mem_image_of_mem _ hx)
  have hcoord : ∀ x ∈ A, σ ≤ x.1 ∧ x.1 ≤ R₀ ∧ -R₀ ≤ x.2.1 ∧ x.2.1 ≤ R₀ ∧
      -R₀ ≤ x.2.2 ∧ x.2.2 ≤ R₀ := by
    intro x hx
    have a1 : ‖x.1‖ ≤ R₀ := (norm_fst_le x).trans (hnorm x hx)
    have a2 : ‖x.2.1‖ ≤ R₀ := ((norm_fst_le x.2).trans (norm_snd_le x)).trans (hnorm x hx)
    have a3 : ‖x.2.2‖ ≤ R₀ := ((norm_snd_le x.2).trans (norm_snd_le x)).trans (hnorm x hx)
    rw [Real.norm_eq_abs] at a1 a2 a3
    have b1 := abs_le.mp a1
    have b2 := abs_le.mp a2
    have b3 := abs_le.mp a3
    exact ⟨hσA x hx, b1.2, b2.1, b2.2, b3.1, b3.2⟩
  -- the sum of norms is continuous, hence bounded on the compact `A`
  have hcont : ∀ i : Fin 2, Continuous (fun x => flatTranspose ν μ Ψ x i) :=
    fun i => (deqTransposeTest ν μ hΨ i).1
  have hgc : Continuous (fun x : Coord => ∑ i : Fin 2, ‖flatTranspose ν μ Ψ x i‖) :=
    continuous_finsetSum _ (fun i _ => (hcont i).norm)
  obtain ⟨K₁, hK₁⟩ := (hA.image hgc).bddAbove
  -- the sum vanishes off `A`
  have hzero : ∀ x, x ∉ A → ∑ i : Fin 2, ‖flatTranspose ν μ Ψ x i‖ = 0 := by
    intro x hx
    have hf0 : flatTranspose ν μ Ψ x 0 = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => flatTranspose ν μ Ψ y 0)
        (fun h => hx (Set.mem_union_left _ h))
    have hf1 : flatTranspose ν μ Ψ x 1 = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => flatTranspose ν μ Ψ y 1)
        (fun h => hx (Set.mem_union_right _ h))
    simp [Fin.sum_univ_two, hf0, hf1]
  refine ⟨σ, R₀, R₀, max K₁ 0, hσ, le_max_right _ _, fun x => ⟨?_, ?_⟩⟩
  · by_cases hx : x ∈ A
    · exact (hK₁ (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
    · rw [hzero x hx]
      exact le_max_right _ _
  · intro hxb
    apply hzero x
    intro hxA
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcoord x hxA
    exact hxb ⟨⟨h1, h2⟩, ⟨⟨h3, h4⟩, ⟨h5, h6⟩⟩⟩

end UnforcedLeray.Short.IIb
