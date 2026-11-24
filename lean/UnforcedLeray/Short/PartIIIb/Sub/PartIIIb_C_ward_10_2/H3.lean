import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H2

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (3): the cylinder kernel

Source of record: `the November 2 reference manuscript` (73 pages), 3687-3697:
translation-invariant majorant `C D⁻²(D² + |z - z_src|²)⁻¹ 1_{|y' - z'_src| ≤ CD}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The cylinder integral over `ℝ³`. -/
theorem w2_lintegral_cyl (f : ℝ → ℝ≥0∞) (hf : Measurable f) (A : ℝ) :
    ∫⁻ x : Space, (if |x 0| ≤ A ∧ |x 1| ≤ A then f (x 2) else 0) =
      ENNReal.ofReal (2 * A) ^ 2 * ∫⁻ w, f w := by
  have hmp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans
    (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)
  set e : Space ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)
    with he
  set F : ℝ × (Fin 2 → ℝ) → ℝ≥0∞ := fun p =>
    if |p.2 0| ≤ A ∧ |p.2 1| ≤ A then f p.1 else 0 with hF
  have h1 : ∫⁻ x : Space, (if |x 0| ≤ A ∧ |x 1| ≤ A then f (x 2) else 0) =
      ∫⁻ p : ℝ × (Fin 2 → ℝ), F p := by
    rw [← hmp.lintegral_comp_emb e.measurableEmbedding F]
    rfl
  rw [h1]
  set S : Set (Fin 2 → ℝ) := Set.Icc (fun _ => -A) (fun _ => A) with hS
  have hSm : MeasurableSet S := measurableSet_Icc
  have hFeq : ∀ p : ℝ × (Fin 2 → ℝ), F p = S.indicator (fun _ => f p.1) p.2 := by
    intro p
    simp only [hF, hS, Set.indicator, Set.mem_Icc, Pi.le_def, Fin.forall_fin_two, abs_le]
    by_cases h : (-A ≤ p.2 0 ∧ p.2 0 ≤ A) ∧ (-A ≤ p.2 1 ∧ p.2 1 ≤ A)
    · rw [if_pos h, if_pos]
      exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩
    · rw [if_neg h, if_neg]
      intro h'
      exact h ⟨⟨h'.1.1, h'.2.1⟩, ⟨h'.1.2, h'.2.2⟩⟩
  have hFm' : Measurable F := by
    have : Measurable (fun p : ℝ × (Fin 2 → ℝ) => S.indicator (fun _ => f p.1) p.2) :=
      Measurable.ite (measurable_snd hSm) (hf.comp measurable_fst) measurable_const
    have e2 : F = fun p : ℝ × (Fin 2 → ℝ) => S.indicator (fun _ => f p.1) p.2 := funext hFeq
    rw [e2]; exact this
  rw [Measure.volume_eq_prod, lintegral_prod _ hFm'.aemeasurable]
  have hvol : volume S = ENNReal.ofReal (2 * A) ^ 2 := by
    rw [hS, Real.volume_Icc_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show A - -A = 2 * A by ring]
  calc ∫⁻ a, ∫⁻ v, F (a, v) = ∫⁻ a, f a * ENNReal.ofReal (2 * A) ^ 2 := by
        refine lintegral_congr fun a => ?_
        simp_rw [hFeq]
        rw [lintegral_indicator_const hSm, hvol]
    _ = ENNReal.ofReal (2 * A) ^ 2 * ∫⁻ w, f w := by
        rw [lintegral_mul_const _ hf, mul_comm]

end UnforcedLeray.Short.PartIIIb.Concrete
end
