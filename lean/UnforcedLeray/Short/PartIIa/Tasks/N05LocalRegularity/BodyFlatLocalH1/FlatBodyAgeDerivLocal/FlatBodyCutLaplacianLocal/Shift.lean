import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.Basic
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.CylDefs

/-!
# Helpers for `PartII-a:N05/2/2/1`: one period cell against another

Source: `the November 2 reference manuscript`, lines 1794-1799 (constants
independent of the number of cells). For an a.e. `q`-periodic `G ≥ 0` the integral over the cell
`(0, c]` equals the integral over the centred cell `[-c/2, c/2)` of `Cyl.avgμ`; this compares the
cell norm `cellMeasure c` with the normalised cylinder norm `cylMeasL c = ds × dq/c dη` of the
cylinder heat estimate (`IIb.CylHeatMaxReg`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.Short.IIb (Coord)

theorem measurableSet_strip3 {S : Set ℝ} (hS : MeasurableSet S) (a b : ℝ) :
    MeasurableSet (S ×ˢ (Ioc a b ×ˢ (univ : Set ℝ)) : Set Coord) :=
  hS.prod (measurableSet_Ioc.prod MeasurableSet.univ)

/-- Translating a strip by one period. -/
theorem lintegral_strip_shift {c : ℝ} {G : Coord → ℝ≥0∞}
    (hper : ∀ᵐ x : Coord, G (x + qv c) = G x) (S : Set ℝ) (a b : ℝ) :
    ∫⁻ x in S ×ˢ (Ioc a b ×ˢ univ), G x = ∫⁻ x in S ×ˢ (Ioc (a + c) (b + c) ×ˢ univ), G x := by
  have hmp := measurePreserving_add_right (volume : Measure Coord) (qv c)
  have hemb : MeasurableEmbedding (fun x : Coord => x + qv c) :=
    (MeasurableEquiv.addRight (qv c)).measurableEmbedding
  have key := hmp.setLIntegral_comp_preimage_emb hemb G (S ×ˢ (Ioc (a + c) (b + c) ×ˢ univ))
  have hpre : (fun x : Coord => x + qv c) ⁻¹' (S ×ˢ (Ioc (a + c) (b + c) ×ˢ univ)) =
      S ×ˢ (Ioc a b ×ˢ univ) := by
    ext x
    simp only [mem_preimage, mem_prod, mem_Ioc, mem_univ, and_true, add_qv_fst, add_qv_snd_fst]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
  rw [hpre] at key
  rw [← key]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hper] with x hx
  exact hx.symm

theorem disjoint_strip3 (S : Set ℝ) {a b d : ℝ} :
    Disjoint (S ×ˢ (Ioc a b ×ˢ (univ : Set ℝ)) : Set Coord) (S ×ˢ (Ioc b d ×ˢ univ)) := by
  rw [Set.disjoint_left]
  rintro x ⟨_, ⟨_, h1⟩, _⟩ ⟨_, ⟨h2, _⟩, _⟩
  linarith

theorem strip3_union (S : Set ℝ) {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    (S ×ˢ (Ioc a d ×ˢ (univ : Set ℝ)) : Set Coord) =
      S ×ˢ (Ioc a b ×ˢ univ) ∪ S ×ˢ (Ioc b d ×ˢ univ) := by
  rw [← Set.prod_union, ← Set.union_prod, Ioc_union_Ioc_eq_Ioc hab hbd]

/-- The cell `(0, c]` and the centred cell `[-c/2, c/2)` carry the same integral of an a.e.
`q`-periodic function. -/
theorem lintegral_cell_eq_centered {c : ℝ} (hc : 0 < c) {G : Coord → ℝ≥0∞}
    (hper : ∀ᵐ x : Coord, G (x + qv c) = G x) {S : Set ℝ} (hS : MeasurableSet S) :
    ∫⁻ x in S ×ˢ (Ioc 0 c ×ˢ univ), G x =
      ∫⁻ x in S ×ˢ (Ico (-c / 2) (c / 2) ×ˢ univ), G x := by
  rw [strip3_union S (a := 0) (b := c / 2) (d := c) (by linarith) (by linarith),
    lintegral_union (measurableSet_strip3 hS _ _) (disjoint_strip3 S)]
  have hsh := lintegral_strip_shift hper S (-c / 2) 0
  rw [show -c / 2 + c = c / 2 by ring, zero_add] at hsh
  rw [← hsh, add_comm, ← lintegral_union (measurableSet_strip3 hS _ _) (disjoint_strip3 S),
    ← strip3_union S (by linarith) (by linarith)]
  refine setLIntegral_congr ?_
  have h1 : (Ioc (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) =ᵐ[(volume : Measure ℝ).prod
      (volume : Measure ℝ)] Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) :=
    Measure.set_prod_ae_eq Ico_ae_eq_Ioc.symm (ae_eq_refl _)
  have h2 : (S ×ˢ (Ioc (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) : Set Coord) =ᵐ[(volume : Measure ℝ).prod
      ((volume : Measure ℝ).prod (volume : Measure ℝ))]
        S ×ˢ (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) :=
    Measure.set_prod_ae_eq (ae_eq_refl _) h1
  exact h2

/-- Two adjacent cells `(-c, c]`. -/
theorem lintegral_two_cells {c : ℝ} (hc : 0 < c) {G : Coord → ℝ≥0∞}
    (hper : ∀ᵐ x : Coord, G (x + qv c) = G x) {S : Set ℝ} (hS : MeasurableSet S) :
    ∫⁻ x in S ×ˢ (Ioc (-c) c ×ˢ univ), G x = 2 * ∫⁻ x in S ×ˢ (Ioc 0 c ×ˢ univ), G x := by
  rw [strip3_union S (a := -c) (b := 0) (d := c) (by linarith) (by linarith),
    lintegral_union (measurableSet_strip3 hS _ _) (disjoint_strip3 S)]
  have hsh := lintegral_strip_shift hper S (-c) 0
  rw [show -c + c = 0 by ring, zero_add] at hsh
  rw [hsh, two_mul]

/-- The normalised cylinder measure: `∫ G d(cylMeasL c) = c⁻¹ ∫_{ℝ × [-c/2,c/2) × ℝ} G`. -/
theorem lintegral_cylMeas (c : ℝ) (G : Coord → ℝ≥0∞) :
    ∫⁻ x, G x ∂(cylMeasL c) =
      ENNReal.ofReal c⁻¹ * ∫⁻ x in univ ×ˢ (Ico (-c / 2) (c / 2) ×ˢ univ), G x := by
  have hprod : (volume : Measure ℝ).prod (UnforcedLeray.Cyl.cellμ c) =
      (volume : Measure Coord).restrict (univ ×ˢ (Ico (-c / 2) (c / 2) ×ˢ univ)) := by
    unfold UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell
    rw [show (volume : Measure Coord) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) from rfl,
      ← Measure.prod_restrict, Measure.restrict_univ]
  unfold cylMeasL UnforcedLeray.Cyl.avgμ
  rw [Measure.prod_smul_right, lintegral_smul_measure, hprod, smul_eq_mul]

theorem lintegral_univ_eq_Ioi {T : Set (ℝ × ℝ)} (hT : MeasurableSet T) {G : Coord → ℝ≥0∞}
    (hpos : ∀ x : Coord, x.1 ≤ 0 → G x = 0) :
    ∫⁻ x in univ ×ˢ T, G x = ∫⁻ x in Ioi 0 ×ˢ T, G x := by
  have hU : (univ ×ˢ T : Set Coord) = Iic 0 ×ˢ T ∪ Ioi 0 ×ˢ T := by
    rw [← Set.union_prod, Iic_union_Ioi]
  have hD : Disjoint (Iic 0 ×ˢ T : Set Coord) (Ioi 0 ×ˢ T) := by
    rw [Set.disjoint_left]
    rintro x ⟨h1, _⟩ ⟨h2, _⟩
    exact absurd (mem_Ioi.1 h2) (not_lt.2 (mem_Iic.1 h1))
  rw [hU, lintegral_union (measurableSet_Ioi.prod hT) hD]
  have h0 : ∫⁻ x in Iic 0 ×ˢ T, G x = 0 := by
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) ?_, lintegral_zero]
    filter_upwards [ae_restrict_mem (measurableSet_Iic.prod hT)] with x hx
    exact hpos x hx.1
  rw [h0, zero_add]

/-- The cell norm is at most `c` times the cylinder norm (a.e. periodic `G`). -/
theorem lintegral_cell_le_cylMeas {c : ℝ} (hc : 0 < c) {G : Coord → ℝ≥0∞}
    (hper : ∀ᵐ x : Coord, G (x + qv c) = G x) :
    ∫⁻ x in UnforcedLeray.B0220.cell c, G x ≤ ENNReal.ofReal c * ∫⁻ x, G x ∂(cylMeasL c) := by
  rw [lintegral_cylMeas, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]
  change ∫⁻ x in Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ), G x ≤ _
  rw [lintegral_cell_eq_centered hc hper measurableSet_Ioi]
  exact lintegral_mono_set (Set.prod_mono (subset_univ _) subset_rfl)

/-- For an a.e. periodic `G` vanishing for `s ≤ 0`, the cylinder norm is `c⁻¹` times the cell
norm. -/
theorem lintegral_cylMeas_eq_cell {c : ℝ} (hc : 0 < c) {G : Coord → ℝ≥0∞}
    (hper : ∀ᵐ x : Coord, G (x + qv c) = G x) (hpos : ∀ x : Coord, x.1 ≤ 0 → G x = 0) :
    ∫⁻ x, G x ∂(cylMeasL c) = ENNReal.ofReal c⁻¹ * ∫⁻ x in UnforcedLeray.B0220.cell c, G x := by
  rw [lintegral_cylMeas, lintegral_univ_eq_Ioi (measurableSet_Ico.prod MeasurableSet.univ) hpos]
  change _ = _ * ∫⁻ x in Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ), G x
  rw [lintegral_cell_eq_centered hc hper measurableSet_Ioi]

/-- `‖f‖_{L²}^2` as a lower integral. -/
theorem sq_eLpNorm_two {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) (by norm_num)
  simpa using h

end UnforcedLeray.Short.PartIIa.FBCLL
