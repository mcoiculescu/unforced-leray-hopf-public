import UnforcedLeray.Short.PartIIIa.FlatCausal

/-!
# Part III-a: shared measurability helpers for the flat causal norms

Measurability of the Frobenius norm `tnorm2` of a measurable tensor field and of the gain
conjugation `g⁻¹ b` of a measurable vector field (`FlatCausal.lean`, SP 3405-3446).

These two lemmas were previously stated twice, in `ComposeCorollary.lean` and in
`Sub/PartIII-a_T18_3_2.lean`; both now import this file, so the free solver
`T18_FreeCausal.lean` can be imported next to `ComposeCorollary.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem measurable_tnorm2 {α : Type*} [MeasurableSpace α] {T : α → Fin 2 → Fin 2 → ℂ}
    (hT : ∀ i j, Measurable fun p => T p i j) : Measurable fun p => tnorm2 (T p) := by
  have h00 := (hT 0 0).norm
  have h01 := (hT 0 1).norm
  have h10 := (hT 1 0).norm
  have h11 := (hT 1 1).norm
  unfold tnorm2
  simp only [Fin.sum_univ_two]
  exact Real.continuous_sqrt.measurable.comp
    (((h00.pow_const 2).add (h01.pow_const 2)).add ((h10.pow_const 2).add (h11.pow_const 2)))

theorem measurable_gainConj_vec {γ ν : ℝ} {f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hf : ∀ i, Measurable fun p => f p i) (i : Fin 2) :
    Measurable fun p => gainConj γ ν f p i := by
  have hg : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ := by
    unfold gainG; fun_prop
  exact hg.smul (hf i)

end UnforcedLeray.Short.IIIa
