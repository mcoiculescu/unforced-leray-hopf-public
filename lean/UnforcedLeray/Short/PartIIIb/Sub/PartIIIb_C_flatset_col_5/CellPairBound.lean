import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5

/-!
# Helper: the cell pairing `x ↦ ⟨x, φ⟩` on `X_{m,c}` is linear and bounded

For a cylinder test `φ` (bounded on the cell) the pairing `cellPair φ x = ∫_cell x φ` is linear in
`x` and satisfies `‖cellPair φ x‖ ≤ K ‖x‖` (the cell `L¹` bound `lintegral_cell_enorm_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem cylTest_bound_cell {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ B0579.cell c, ‖φ y‖ ≤ M := by
  obtain ⟨R, hR⟩ := hφ.band
  have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-|R|) |R|) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y hy => ?_⟩
  have hy' := hy
  simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at hy'
  by_cases h : |y.2| ≤ |R|
  · have hmem : y ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-|R|) |R| :=
      ⟨⟨hy'.1, hy'.2.le⟩, abs_le.1 h⟩
    exact (hM y hmem).trans (le_max_left _ _)
  · have h0 : φ y = 0 := hR y (lt_of_le_of_lt (le_abs_self R) (not_le.1 h))
    rw [h0, norm_zero]
    exact le_max_right _ _

theorem cell_ae_of_mem {c : ℝ} {P : ℝ × ℝ → Prop} (h : ∀ y ∈ B0579.cell c, P y) :
    ∀ᵐ y ∂(volume.restrict (B0579.cell c)), P y :=
  ae_restrict_of_forall_mem (B0579.measurableSet_cell c) h

theorem xFn_integrableOn_cell {c m : ℝ} [hm : Fact (1 < m)] (x : Xmc c m) :
    IntegrableOn (xFn x) (B0579.cell c) := xFn_integrableOn x

/-- The `L¹` norm of `xFn x` on the cell is bounded by the `X_{m,c}` norm. -/
theorem lintegral_norm_cell_le {c m : ℝ} [hm : Fact (1 < m)] (x : Xmc c m) :
    ∫ y in B0579.cell c, ‖xFn x y‖ ≤ (B0592.weightConst m).toReal * ‖x‖ := by
  have hX : AEStronglyMeasurable (xFn x) (volume.restrict (B0579.cell c)) :=
    (xFn_integrableOn x).1
  rw [integral_norm_eq_lintegral_enorm hX]
  have hne : B0592.weightConst m ≠ ⊤ := (B0592.weightConst_lt_top hm.out).ne
  calc (∫⁻ y in B0579.cell c, ‖xFn x y‖ₑ).toReal
      ≤ (B0592.weightConst m * ENNReal.ofReal ‖x‖).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hne ENNReal.ofReal_ne_top)
          (lintegral_cell_enorm_le (x : XAmb c m))
    _ = (B0592.weightConst m).toReal * ‖x‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]

theorem integrableOn_xFn_mul_of {c m : ℝ} [hm : Fact (1 < m)] {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest c φ) (x : Xmc c m) :
    IntegrableOn (fun y => xFn x y * (φ y : ℂ)) (B0579.cell c) := by
  obtain ⟨M, hM0, hM⟩ := cylTest_bound_cell hφ
  have hmeas : AEStronglyMeasurable (fun y => xFn x y * (φ y : ℂ))
      (volume.restrict (B0579.cell c)) :=
    (xFn_integrableOn x).1.mul
      (Complex.continuous_ofReal.comp hφ.continuous).aestronglyMeasurable
  refine Integrable.mono' ((xFn_integrableOn x).norm.const_mul M) hmeas ?_
  refine cell_ae_of_mem fun y hy => ?_
  rw [norm_mul, Complex.norm_real, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM y hy) (norm_nonneg _)

/-- The cell pairing `⟨x, φ⟩ = ∫_cell x φ` is bounded by the `X_{m,c}` norm. -/
theorem cellPair_bound {c m : ℝ} [hm : Fact (1 < m)] {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest c φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Xmc c m, ‖cellPair φ x‖ ≤ K * ‖x‖ := by
  obtain ⟨M, hM0, hM⟩ := cylTest_bound_cell hφ
  refine ⟨M * (B0592.weightConst m).toReal, mul_nonneg hM0 ENNReal.toReal_nonneg,
    fun x => ?_⟩
  have hI : Integrable (fun y => M * ‖xFn x y‖) (volume.restrict (B0579.cell c)) :=
    (xFn_integrableOn x).norm.const_mul M
  calc ‖cellPair φ x‖ = ‖∫ y in B0579.cell c, xFn x y * (φ y : ℂ)‖ := rfl
    _ ≤ ∫ y in B0579.cell c, ‖xFn x y * (φ y : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in B0579.cell c, M * ‖xFn x y‖ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hI ?_
        refine cell_ae_of_mem fun y hy => ?_
        show ‖xFn x y * (φ y : ℂ)‖ ≤ M * ‖xFn x y‖
        rw [norm_mul, Complex.norm_real, mul_comm M]
        exact mul_le_mul_of_nonneg_left (hM y hy) (norm_nonneg _)
    _ = M * ∫ y in B0579.cell c, ‖xFn x y‖ := integral_const_mul M _
    _ ≤ M * ((B0592.weightConst m).toReal * ‖x‖) :=
        mul_le_mul_of_nonneg_left (lintegral_norm_cell_le x) hM0
    _ = M * (B0592.weightConst m).toReal * ‖x‖ := by ring

theorem cellPair_sub' {c m : ℝ} [Fact (1 < m)] {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest c φ) (x y : Xmc c m) :
    cellPair φ (x - y) = cellPair φ x - cellPair φ y := by
  unfold cellPair
  rw [← integral_sub (integrableOn_xFn_mul_of hφ x) (integrableOn_xFn_mul_of hφ y)]
  refine integral_congr_ae ?_
  filter_upwards [xFn_sub x y] with p hp
  rw [hp]
  ring

theorem cellPair_add' {c m : ℝ} [Fact (1 < m)] {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest c φ) (x y : Xmc c m) :
    cellPair φ (x + y) = cellPair φ x + cellPair φ y := by
  unfold cellPair
  rw [← integral_add (integrableOn_xFn_mul_of hφ x) (integrableOn_xFn_mul_of hφ y)]
  refine integral_congr_ae ?_
  filter_upwards [xFn_add x y] with p hp
  rw [hp]
  ring

theorem cellPair_smul' {c m : ℝ} [Fact (1 < m)] {φ : ℝ × ℝ → ℝ}
    (a : ℂ) (x : Xmc c m) :
    cellPair φ (a • x) = a * cellPair φ x := by
  unfold cellPair
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [xFn_smul a x] with p hp
  rw [hp]
  ring

/-- The cell pairing `⟨·, φ⟩` as a continuous linear functional on `X_{m,c}`. -/
def cellPairCLM {c m : ℝ} [Fact (1 < m)] {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    Xmc c m →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => cellPair φ x
      map_add' := fun x y => cellPair_add' hφ x y
      map_smul' := fun a x => by
        rw [RingHom.id_apply]
        exact cellPair_smul' a x }
    (Classical.choose (cellPair_bound (m := m) hφ))
    (fun x => by
      have := (Classical.choose_spec (cellPair_bound (m := m) hφ)).2 x
      exact this)

theorem cellPairCLM_apply {c m : ℝ} [Fact (1 < m)] {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest c φ) (x : Xmc c m) : cellPairCLM hφ x = cellPair φ x := rfl

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
