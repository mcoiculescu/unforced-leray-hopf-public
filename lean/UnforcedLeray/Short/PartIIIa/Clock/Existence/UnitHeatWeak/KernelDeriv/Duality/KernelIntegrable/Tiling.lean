import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1_2_1

/-!
# Tiling of the plane by translates of the cell (helper for `DualityKernelIntegrable`)

For `c > 0` the translates `{a | a + (k c, 0) ∈ cell c}`, `k : ℤ`, are pairwise disjoint and cover
the plane, so every nonnegative measurable `f` satisfies
`∫⁻ f = ∑_k ∫⁻_{cell} f(· - (k c, 0))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Function
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist.KI

lemma mem_shift_iff (c : ℝ) (k : ℤ) (a : ℝ × ℝ) :
    a + ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c ↔
      -(c / 2) ≤ a.1 + (k : ℝ) * c ∧ a.1 + (k : ℝ) * c < c / 2 := by
  simp only [UnforcedLeray.B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true,
    Prod.fst_add]

lemma cell_measurable (c : ℝ) : MeasurableSet (UnforcedLeray.B0579.cell c) :=
  measurableSet_Ico.prod MeasurableSet.univ

lemma tile_measurable (c : ℝ) (k : ℤ) :
    MeasurableSet {a : ℝ × ℝ | a + ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c} :=
  (cell_measurable c).preimage (measurable_id.add_const _)

lemma tile_disjoint (c : ℝ) (hc : 0 < c) :
    Pairwise (Disjoint on fun k : ℤ =>
      {a : ℝ × ℝ | a + ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c}) := by
  intro j k hjk
  rw [Function.onFun, Set.disjoint_left]
  intro a ha hb
  simp only [Set.mem_setOf_eq, mem_shift_iff] at ha hb
  apply hjk
  have h1 : ((k : ℝ) - j) * c < 1 * c := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have h2 : -1 * c < ((k : ℝ) - j) * c := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have h1' : (k : ℝ) - j < 1 := lt_of_mul_lt_mul_right h1 hc.le
  have h2' : -1 < (k : ℝ) - j := lt_of_mul_lt_mul_right h2 hc.le
  have h1'' : k - j < 1 := by
    have : ((k - j : ℤ) : ℝ) < 1 := by push_cast; linarith
    exact_mod_cast this
  have h2'' : -1 < k - j := by
    have : (-1 : ℝ) < ((k - j : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

lemma tile_iUnion (c : ℝ) (hc : 0 < c) :
    (⋃ k : ℤ, {a : ℝ × ℝ | a + ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c}) = univ := by
  ext a
  simp only [mem_iUnion, Set.mem_setOf_eq, mem_univ, iff_true]
  refine ⟨-⌊(a.1 + c / 2) / c⌋, ?_⟩
  rw [mem_shift_iff]
  have h1 := Int.floor_le ((a.1 + c / 2) / c)
  have h2 := Int.lt_floor_add_one ((a.1 + c / 2) / c)
  set n := ⌊(a.1 + c / 2) / c⌋ with hn
  have e1 : (n : ℝ) * c ≤ a.1 + c / 2 := by
    have := (le_div_iff₀ hc).1 h1
    linarith
  have e2 : a.1 + c / 2 < (n : ℝ) * c + c := by
    have := (div_lt_iff₀ hc).1 h2
    linarith [show ((n : ℝ) + 1) * c = (n : ℝ) * c + c by ring]
  push_cast
  constructor <;> linarith

/-- Tiling identity: a nonnegative measurable function integrates over the plane as the sum of
its integrals over the cell translated by `(-(k c), 0)`. -/
theorem lintegral_eq_tsum_minus (c : ℝ) (hc : 0 < c) (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p, f p = ∑' k : ℤ, ∫⁻ p in UnforcedLeray.B0579.cell c, f (p - ((k : ℝ) * c, (0 : ℝ))) := by
  rw [← setLIntegral_univ, ← tile_iUnion c hc,
    lintegral_iUnion (fun k => tile_measurable c k) (tile_disjoint c hc)]
  refine tsum_congr fun k => ?_
  have hv := (measurePreserving_add_right (volume : Measure (ℝ × ℝ)) ((k : ℝ) * c, (0 : ℝ))).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight ((k : ℝ) * c, (0 : ℝ)))
    (fun b => f (b - ((k : ℝ) * c, (0 : ℝ)))) (UnforcedLeray.B0579.cell c)
  simp only [add_sub_cancel_right] at hv
  exact hv

end UnforcedLeray.Short.IIIa.Exist.KI
