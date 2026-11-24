import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2

/-!
# `PartIII-b:C/grad/3/5/2/2` task 2: jet bounds of the prefactor `-2 a⁻¹`

Source `the November 2 reference manuscript`
5063-5079, 4974-4980.  The function `q ↦ -2 (1 + ν q₁)⁻¹` is smooth on `{s > 0}`; its derivatives of
order `≤ 3` are continuous there, hence bounded on the compact set `closure U ⊆ {s > 0}`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Jets of order `≤ 3` of a function smooth on an open set `S` are bounded on `U` when
`closure U ⊆ S` is bounded. -/
lemma ai_compact {S : Set Chart} (hS : IsOpen S) (f : Chart → ℝ) (hf : ContDiffOn ℝ 3 f S)
    (U : Set Chart) (hUo : IsOpen U) (hUS : closure U ⊆ S) (hbd : Bornology.IsBounded (closure U)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : ℕ, i ≤ 3 → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ i f U p‖ ≤ M := by
  have hK : IsCompact (closure U) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hbd
  have hbound : ∀ i : ℕ, i ≤ 3 → ∃ C : ℝ, ∀ x ∈ closure U, ‖iteratedFDerivWithin ℝ i f S x‖ ≤ C := by
    intro i hi
    have hcont : ContinuousOn (iteratedFDerivWithin ℝ i f S) S :=
      hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) hS.uniqueDiffOn
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hUS)
    exact ⟨C, hC⟩
  have hUeq : ∀ i : ℕ, ∀ p ∈ U, iteratedFDerivWithin ℝ i f U p = iteratedFDerivWithin ℝ i f S p := by
    intro i p hp
    exact (iteratedFDerivWithin_of_isOpen i hUo hp).trans
      (iteratedFDerivWithin_of_isOpen i hS (hUS (subset_closure hp))).symm
  obtain ⟨C0, hC0⟩ := hbound 0 (by norm_num)
  obtain ⟨C1, hC1⟩ := hbound 1 (by norm_num)
  obtain ⟨C2, hC2⟩ := hbound 2 (by norm_num)
  obtain ⟨C3, hC3⟩ := hbound 3 (by norm_num)
  refine ⟨|C0| + |C1| + |C2| + |C3|, by positivity, ?_⟩
  intro i hi p hp
  rw [hUeq i p hp]
  have hpc : p ∈ closure U := subset_closure hp
  have a0 := abs_nonneg C0
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg C2
  have a3 := abs_nonneg C3
  have b0 := le_abs_self C0
  have b1 := le_abs_self C1
  have b2 := le_abs_self C2
  have b3 := le_abs_self C3
  interval_cases i
  · have := hC0 p hpc
    linarith
  · have := hC1 p hpc
    linarith
  · have := hC2 p hpc
    linarith
  · have := hC3 p hpc
    linarith

theorem ageInvJets : AgeInvJets := by
  intro ν hν U hUo hUc hcl hbd
  have h1 : ContDiff ℝ 3 (fun q : Chart => ageA ν q.1) := by
    unfold ageA
    fun_prop
  have hf : ContDiffOn ℝ 3 (fun q : Chart => -2 * (ageA ν q.1)⁻¹) {p : Chart | 0 < p.1} :=
    (contDiffOn_const (c := (-2 : ℝ))).mul
      (h1.contDiffOn.inv (fun p hp => psc2_ageA_ne ν hν p hp))
  exact ai_compact psc2_isOpen_pos _ hf U hUo hcl hbd

end UnforcedLeray.Short.PartIIIb.Concrete
