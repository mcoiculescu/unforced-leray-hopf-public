import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.Dil

/-!
# `PartIII-a:T21/2/2/2/1/3` leaf `RescaleMemLp` (SP 3052-3058)

The weighted `L²` clause: `χ ∈ L²(C_c, ⟨y⟩^{-2m})` implies `y ↦ a χ(√a y)` is in
`L²(C_{c/√a}, ⟨y⟩^{-2m})`. The density comparison and the lintegral change of variables are in
`Dil.lean` (`lintegral_cellMeasure_dilate`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal
open UnforcedLeray

theorem rescaleMemLp : UnforcedLeray.Short.IIIa.E0.RescaleMemLp := by
  intro m c a hc ha χ hχ
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hT : Measurable (fun y : ℝ × ℝ => Real.sqrt a • y) := measurable_const_smul _
  -- the pushforward of the moving weighted measure is absolutely continuous w.r.t. the fixed one
  have hac : Measure.map (fun y : ℝ × ℝ => Real.sqrt a • y)
      (B0579.cellMeasure (UnforcedLeray.Short.IIIa.cellLen c a) (-m)) ≪
        B0579.cellMeasure c (-m) := by
    apply UnforcedLeray.Short.IIIa.E0.RsDil.ac_of_preimage hT
    intro S hS hS0
    have hF := UnforcedLeray.Short.IIIa.E0.RsDil.lintegral_cellMeasure_dilate hc ha (-m)
      (S.indicator (1 : ℝ × ℝ → ℝ≥0∞))
    rw [lintegral_indicator_one hS, hS0, mul_zero, mul_zero] at hF
    have hEq : B0579.cellMeasure (UnforcedLeray.Short.IIIa.cellLen c a) (-m)
        ((fun y : ℝ × ℝ => Real.sqrt a • y) ⁻¹' S) =
        ∫⁻ y, S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (Real.sqrt a • y)
          ∂(B0579.cellMeasure (UnforcedLeray.Short.IIIa.cellLen c a) (-m)) := by
      rw [← lintegral_indicator_one (hT hS)]
      congr 1
    rw [hEq]
    exact le_antisymm hF zero_le
  have hχm : AEStronglyMeasurable χ (B0579.cellMeasure c (-m)) := hχ.aestronglyMeasurable
  have hgm : AEStronglyMeasurable
      (fun y : ℝ × ℝ => ((a : ℝ) : ℂ) * χ (Real.sqrt a • y))
      (B0579.cellMeasure (UnforcedLeray.Short.IIIa.cellLen c a) (-m)) :=
    (hχm.comp_quasiMeasurePreserving ⟨hT, hac⟩).const_mul _
  have hfun : (fun y : ℝ × ℝ => ((a : ℝ) : ℂ) * χ (Real.sqrt a * y.1, Real.sqrt a * y.2)) =
      fun y : ℝ × ℝ => ((a : ℝ) : ℂ) * χ (Real.sqrt a • y) := by
    funext y
    rw [UnforcedLeray.Short.IIIa.E0.RsDil.smul_sqrt_eq]
  rw [hfun]
  refine ⟨hgm, ?_⟩
  -- finiteness of the weighted `L²` norm of `χ` on the fixed cell
  have hx : UnforcedLeray.Short.IIIa.xNorm c (-m) χ ≠ ⊤ := hχ.2.ne
  have hX : ∫⁻ x, ‖χ x‖ₑ ^ 2 ∂(B0579.cellMeasure c (-m)) ≠ ⊤ := by
    have h := UnforcedLeray.Short.IIIa.XND.xNorm_sq c (-m) χ
    rw [← h]
    exact ENNReal.pow_ne_top hx
  have hmain : ∫⁻ y, ‖χ (Real.sqrt a • y)‖ₑ ^ 2
      ∂(B0579.cellMeasure (UnforcedLeray.Short.IIIa.cellLen c a) (-m)) ≠ ⊤ := by
    have hk := UnforcedLeray.Short.IIIa.E0.RsDil.lintegral_cellMeasure_dilate hc ha (-m)
      (fun x => ‖χ x‖ₑ ^ 2)
    refine ne_top_of_le_ne_top ?_ hk
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX)
  have hsq : ∀ y : ℝ × ℝ, ‖((a : ℝ) : ℂ) * χ (Real.sqrt a • y)‖ₑ ^ 2 =
      ENNReal.ofReal (a ^ 2) * ‖χ (Real.sqrt a • y)‖ₑ ^ 2 :=
    fun y => UnforcedLeray.Short.IIIa.XND.enorm_real_mul_sq a _
  have hfinal : ∫⁻ y, ‖((a : ℝ) : ℂ) * χ (Real.sqrt a • y)‖ₑ ^ 2
      ∂(B0579.cellMeasure (UnforcedLeray.Short.IIIa.cellLen c a) (-m)) ≠ ⊤ := by
    simp_rw [hsq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmain
  rw [UnforcedLeray.Short.IIIa.XND.eLpNorm_two_eq_lintegral']
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfinal
