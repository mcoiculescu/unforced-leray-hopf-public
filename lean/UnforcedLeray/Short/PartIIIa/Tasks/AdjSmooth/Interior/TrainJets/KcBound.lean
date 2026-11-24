import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import UnforcedLeray.Lib.CylinderB.BiotSavart
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The weight `(1 + s²)^{-(m+1)/2}` is integrable on `ℝ` for `m > 0`. -/
theorem kc_weight_integrable (m : ℝ) (hm : 0 < m) :
    Integrable (fun s : ℝ => (1 + s ^ 2) ^ (-((m + 1) / 2))) := by
  have e : (fun s : ℝ => (1 + s ^ 2) ^ (-((m + 1) / 2))) =
      fun s : ℝ => (1 + ‖s‖ ^ 2) ^ (-(m + 1) / 2) := by
    funext s
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  rw [e]
  exact integrable_rpow_neg_one_add_norm_sq (by simp; linarith)

/-- From `P |v| ≤ A` with `P > 0`: `|v| ≤ A P⁻¹`. -/
theorem kc_abs_of_weight {P A v : ℝ} (hP : 0 < P) (h : P * |v| ≤ A) :
    |v| ≤ A * P⁻¹ := by
  have hP' : P ≠ 0 := hP.ne'
  calc |v| = (P * |v|) * P⁻¹ := by field_simp
    _ ≤ A * P⁻¹ := mul_le_mul_of_nonneg_right h (inv_nonneg.2 hP.le)

/-- **`K_c` of a weighted field is bounded** (SP 2081-2084, 3052-3058): the kernel split of
`Cyl.bsKernel_split` with the weight `(1 + (x₂ - y₂)²)^{-(m+1)/2}` of `TjWBdd` gives the bound
`A C₀ + 2 A c ∫ (1 + s²)^{-(m+1)/2}`. -/
theorem tjKcBound : TjKcBound := by
  intro c m hc1 hm g hgcont hgper hbdd S hS
  have hc0 : 0 < c := by linarith
  obtain ⟨A, hA⟩ := hbdd S hS
  have hA0 : 0 ≤ A :=
    le_trans (mul_nonneg (tjWt_pos m _).le (abs_nonneg _)) (hA 0 ⟨le_refl 0, hS⟩ (0, 0))
  set W : ℝ → ℝ := fun s => (1 + s ^ 2) ^ (-((m + 1) / 2)) with hWdef
  have hW0 : ∀ s : ℝ, 0 ≤ W s := fun s => Real.rpow_nonneg (by positivity) _
  have hW1 : ∀ s : ℝ, W s ≤ 1 := fun s =>
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg s]) (by linarith)
  have hWc : Continuous W :=
    (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2).rpow_const
      (fun s => Or.inl (by positivity))
  have hWint : Integrable W := kc_weight_integrable m hm
  obtain ⟨C₀, hC₀, hsplit⟩ := UnforcedLeray.Cyl.bsKernel_split
  have hCell := hsplit c hc1
  have hcell_meas : MeasurableSet (UnforcedLeray.Cyl.cell c) :=
    UnforcedLeray.Cyl.measurableSet_cell c
  have hkn : StronglyMeasurable (UnforcedLeray.Cyl.kNear c) :=
    ((UnforcedLeray.Cyl.measurable_bsKernel c).indicator
      (hcell_meas.inter Metric.isOpen_ball.measurableSet)).stronglyMeasurable
  refine ⟨A * C₀ + 2 * A * (c * ∫ s : ℝ, W s), fun ρ hρ x => ?_⟩
  have hρ0 : 0 ≤ ρ := hρ.1
  set wf : ℝ × ℝ → ℝ := fun y => g (ρ, y) with hwfdef
  have hwfper : UnforcedLeray.Cyl.IsPeriodic c wf := fun z => hgper ρ hρ0 z
  have hkey : tjKc c g (ρ, x) =
      ∫ y in UnforcedLeray.Cyl.cell c, wf (x - y) • UnforcedLeray.Cyl.bsKernel c y := by
    rw [show tjKc c g (ρ, x) = UnforcedLeray.Cyl.K c wf x from rfl]
    exact UnforcedLeray.Cyl.K_eq_reflect hc0 hwfper x
  rw [hkey]
  -- the pointwise majorant on the cell
  have hpt : ∀ y ∈ UnforcedLeray.Cyl.cell c,
      ‖wf (x - y) • UnforcedLeray.Cyl.bsKernel c y‖ ≤
        A * (W (x.2 - y.2) * (‖UnforcedLeray.Cyl.kNear c y‖ + 2)) := by
    intro y hy
    have hK := hCell.2.2 y hy
    have hKb : ‖UnforcedLeray.Cyl.bsKernel c y‖ ≤ ‖UnforcedLeray.Cyl.kNear c y‖ + 2 := by
      rw [hK]
      exact (norm_add_le _ _).trans (add_le_add (le_refl _) (hCell.2.1 y))
    have hwfb : |wf (x - y)| ≤ A * W (x.2 - y.2) := by
      have h := hA ρ hρ (x - y)
      have hP : 0 < (1 + (x - y).2 ^ 2) ^ ((m + 1) / 2) :=
        Real.rpow_pos_of_pos (by positivity) _
      have h2 := kc_abs_of_weight hP h
      have e : ((1 + (x - y).2 ^ 2) ^ ((m + 1) / 2))⁻¹ = W (x.2 - y.2) := by
        rw [← Real.rpow_neg (show (0:ℝ) ≤ 1 + (x - y).2 ^ 2 by positivity)]
        rfl
      calc |wf (x - y)| = |g (ρ, x - y)| := rfl
        _ ≤ A * ((1 + (x - y).2 ^ 2) ^ ((m + 1) / 2))⁻¹ := h2
        _ = A * W (x.2 - y.2) := by rw [e]
    rw [norm_smul, Real.norm_eq_abs]
    calc |wf (x - y)| * ‖UnforcedLeray.Cyl.bsKernel c y‖
        ≤ (A * W (x.2 - y.2)) * (‖UnforcedLeray.Cyl.kNear c y‖ + 2) :=
          mul_le_mul hwfb hKb (norm_nonneg _) (le_trans (abs_nonneg _) hwfb)
      _ = A * (W (x.2 - y.2) * (‖UnforcedLeray.Cyl.kNear c y‖ + 2)) := by ring
  -- integrability of the near part
  have hkn_int : Integrable (UnforcedLeray.Cyl.kNear c)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) :=
    ⟨hkn.aestronglyMeasurable, lt_of_le_of_lt hCell.1 ENNReal.ofReal_lt_top⟩
  have hkn_norm_int : Integrable (fun y => ‖UnforcedLeray.Cyl.kNear c y‖)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := hkn_int.norm
  have hnear : ∫ y in UnforcedLeray.Cyl.cell c, ‖UnforcedLeray.Cyl.kNear c y‖ ≤ C₀ := by
    rw [integral_norm_eq_lintegral_enorm hkn.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hC₀ hCell.1
  -- the weight restricted to the cell
  have hf₁ : Integrable ((Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ)) := by
    rw [integrable_indicator_iff measurableSet_Ico]
    exact integrableOn_const (by simp)
  have hprod : Integrable (fun z : ℝ × ℝ => (Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ) z.1 *
      W (x.2 - z.2)) (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Integrable.mul_prod hf₁ (hWint.comp_sub_left x.2)
  have eInd : (UnforcedLeray.Cyl.cell c).indicator (fun z : ℝ × ℝ => W (x.2 - z.2)) =
      fun z : ℝ × ℝ => (Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ) z.1 * W (x.2 - z.2) := by
    funext z
    by_cases hz : z.1 ∈ Ico (-c / 2) (c / 2)
    · have hzc : z ∈ UnforcedLeray.Cyl.cell c := ⟨hz, mem_univ _⟩
      simp [Set.indicator_apply, hz, hzc]
    · have hzc : z ∉ UnforcedLeray.Cyl.cell c := fun h => hz h.1
      simp [Set.indicator_apply, hz, hzc]
  have hWcell : Integrable (fun z : ℝ × ℝ => W (x.2 - z.2))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    have hI : Integrable ((UnforcedLeray.Cyl.cell c).indicator (fun z : ℝ × ℝ => W (x.2 - z.2)))
        (volume : Measure (ℝ × ℝ)) := by
      rw [eInd]
      exact hprod
    exact (integrable_indicator_iff hcell_meas).1 hI
  -- the cell integral of the weight is `c` times the line integral
  have hint_eq : ∫ y in UnforcedLeray.Cyl.cell c, W (x.2 - y.2) = c * ∫ s : ℝ, W s := by
    have hlen : ∫ t : ℝ, (Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ) t = c := by
      rw [integral_indicator_one measurableSet_Ico, Real.volume_real_Ico]
      rw [show c / 2 - -c / 2 = c by ring]
      exact max_eq_left hc0.le
    calc ∫ y in UnforcedLeray.Cyl.cell c, W (x.2 - y.2)
        = ∫ z : ℝ × ℝ, (UnforcedLeray.Cyl.cell c).indicator (fun z : ℝ × ℝ => W (x.2 - z.2)) z :=
          (integral_indicator (UnforcedLeray.Cyl.measurableSet_cell c)).symm
      _ = ∫ z : ℝ × ℝ, (Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ) z.1 * W (x.2 - z.2) := by
          rw [eInd]
      _ = (∫ t : ℝ, (Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ) t) *
            ∫ t : ℝ, W (x.2 - t) := by
          rw [Measure.volume_eq_prod]
          exact integral_prod_mul (fun t : ℝ => (Ico (-c / 2) (c / 2)).indicator (1 : ℝ → ℝ) t)
            (fun t : ℝ => W (x.2 - t))
      _ = c * ∫ s : ℝ, W s := by
          rw [hlen, integral_sub_left_eq_self]
  -- the majorant
  have e2 : (fun y : ℝ × ℝ => A * (W (x.2 - y.2) * (‖UnforcedLeray.Cyl.kNear c y‖ + 2))) =
      fun y => A * (W (x.2 - y.2) * ‖UnforcedLeray.Cyl.kNear c y‖) + (2 * A) * W (x.2 - y.2) := by
    funext y
    ring
  have hnk_bd : Integrable (fun y : ℝ × ℝ => W (x.2 - y.2) * ‖UnforcedLeray.Cyl.kNear c y‖)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    refine Integrable.mono' hkn_norm_int ?_ ?_
    · exact ((hWc.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable).mul
        hkn_norm_int.aestronglyMeasurable
    · refine Eventually.of_forall fun y => ?_
      show ‖W (x.2 - y.2) * ‖UnforcedLeray.Cyl.kNear c y‖‖ ≤ ‖UnforcedLeray.Cyl.kNear c y‖
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hW0 _) (norm_nonneg _))]
      exact mul_le_of_le_one_left (norm_nonneg _) (hW1 _)
  have h1 : Integrable (fun y : ℝ × ℝ => A * (W (x.2 - y.2) * ‖UnforcedLeray.Cyl.kNear c y‖))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := hnk_bd.const_mul A
  have h2 : Integrable (fun y : ℝ × ℝ => (2 * A) * W (x.2 - y.2))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := hWcell.const_mul (2 * A)
  have hM_int : Integrable (fun y : ℝ × ℝ => A * (W (x.2 - y.2) * (‖UnforcedLeray.Cyl.kNear c y‖ + 2)))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    rw [e2]
    exact h1.add h2
  have hI_eq : ∫ y in UnforcedLeray.Cyl.cell c, A * (W (x.2 - y.2) * (‖UnforcedLeray.Cyl.kNear c y‖ + 2))
      = A * (∫ y in UnforcedLeray.Cyl.cell c, W (x.2 - y.2) * ‖UnforcedLeray.Cyl.kNear c y‖) +
        2 * A * ∫ y in UnforcedLeray.Cyl.cell c, W (x.2 - y.2) := by
    rw [e2, integral_add h1 h2, integral_const_mul, integral_const_mul]
  have hn1 : ∫ y in UnforcedLeray.Cyl.cell c, W (x.2 - y.2) * ‖UnforcedLeray.Cyl.kNear c y‖ ≤ C₀ :=
    le_trans (integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg (hW0 _) (norm_nonneg _))
      hkn_norm_int (Eventually.of_forall fun y => mul_le_of_le_one_left (norm_nonneg _) (hW1 _)))
      hnear
  calc ‖∫ y in UnforcedLeray.Cyl.cell c, wf (x - y) • UnforcedLeray.Cyl.bsKernel c y‖
      ≤ ∫ y in UnforcedLeray.Cyl.cell c, ‖wf (x - y) • UnforcedLeray.Cyl.bsKernel c y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y in UnforcedLeray.Cyl.cell c, A * (W (x.2 - y.2) * (‖UnforcedLeray.Cyl.kNear c y‖ + 2)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hM_int
          ((ae_restrict_iff' hcell_meas).2 (Eventually.of_forall fun y hy => hpt y hy))
    _ = A * (∫ y in UnforcedLeray.Cyl.cell c, W (x.2 - y.2) * ‖UnforcedLeray.Cyl.kNear c y‖) +
        2 * A * ∫ y in UnforcedLeray.Cyl.cell c, W (x.2 - y.2) := hI_eq
    _ ≤ A * C₀ + 2 * A * (c * ∫ s : ℝ, W s) := by
        rw [hint_eq]
        linarith [mul_le_mul_of_nonneg_left hn1 hA0]

end UnforcedLeray.Short.IIIa
