import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_3_2

/-!
# `CcDensityBox`: density of `C_c` in `L²` of the time box

Source `the November 2 reference manuscript`
lines 1556-1583. Let `f = 1_{tBox R} g ∈ L²(ℝ × ℝ³)`, approximate `f` by a continuous compactly
supported `φ` in `L²` (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), and restrict the error to
the box.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private theorem two_ne_zero_ennreal' : (2 : ℝ≥0∞) ≠ 0 := by norm_num

private theorem two_ne_top_ennreal' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num

/-- `L²` bound from a lintegral bound (`eLpNorm` at exponent `2`). -/
theorem lint_sq_le_of_eLpNorm {h : ℝ × Space → CVec3} {c : ℝ≥0∞}
    (hc : eLpNorm h 2 volume ≤ c) : ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ≤ c ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero_ennreal' two_ne_top_ennreal',
    ENNReal.toReal_ofNat] at hc
  have := ENNReal.rpow_le_rpow hc (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one] at this
  exact this

/-- A measurable function with finite `∫⁻ ‖h‖ₑ²` is in `L²`. -/
theorem memLp_two_of_lint {h : ℝ × Space → CVec3} (hm : AEStronglyMeasurable h volume)
    (hI : ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) < ⊤) : MemLp h 2 volume := by
  refine ⟨hm, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero_ennreal' two_ne_top_ennreal',
    ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hI.ne

theorem ccDensityBox : CcDensityBox := by
  intro R g hg hfin η hη
  have hT : MeasurableSet (tBox R) := measurableSet_Icc.prod MeasurableSet.univ
  have hfm : AEStronglyMeasurable ((tBox R).indicator g) volume := hg.indicator hT
  have hI : ∫⁻ x, ‖(tBox R).indicator g x‖ₑ ^ (2 : ℝ) < ⊤ := by
    have heq : ∫⁻ x, ‖(tBox R).indicator g x‖ₑ ^ (2 : ℝ)
        = ∫⁻ x in tBox R, ‖g x‖ₑ ^ (2 : ℝ) := by
      calc ∫⁻ x, ‖(tBox R).indicator g x‖ₑ ^ (2 : ℝ)
          = ∫⁻ x, (tBox R).indicator (fun x => ‖g x‖ₑ ^ (2 : ℝ)) x := by
            refine lintegral_congr fun x => ?_
            by_cases hx : x ∈ tBox R
            · simp only [Set.indicator_of_mem hx]
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, enorm_zero,
                ENNReal.zero_rpow_of_pos (by norm_num)]
        _ = ∫⁻ x in tBox R, ‖g x‖ₑ ^ (2 : ℝ) := lintegral_indicator hT _
    rw [heq]
    exact hfin
  have hfL : MemLp ((tBox R).indicator g) 2 volume := memLp_two_of_lint hfm hI
  set c : ℝ := min 1 η / 2 with hc_def
  have hm0 : 0 < min 1 η := lt_min one_pos hη
  have hc0 : 0 < c := by rw [hc_def]; exact div_pos hm0 two_pos
  have hc2 : c ^ 2 < η := by
    have h1 : min 1 η ≤ 1 := min_le_left _ _
    have h2 : min 1 η ≤ η := min_le_right _ _
    rw [hc_def]
    nlinarith [mul_nonneg hm0.le (sub_nonneg.mpr h1)]
  obtain ⟨φ, hφs, hφapp, hφc, -⟩ :=
    MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le two_ne_top_ennreal' hfL
      (ENNReal.ofReal_pos.mpr hc0).ne'
  refine ⟨φ, hφc, hφs, ?_⟩
  have hstep1 : ∫⁻ x in tBox R, ‖g x - φ x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x, ‖(tBox R).indicator g x - φ x‖ₑ ^ (2 : ℝ) := by
    calc ∫⁻ x in tBox R, ‖g x - φ x‖ₑ ^ (2 : ℝ)
        = ∫⁻ x, (tBox R).indicator (fun x => ‖g x - φ x‖ₑ ^ (2 : ℝ)) x :=
          (lintegral_indicator hT _).symm
      _ ≤ ∫⁻ x, ‖(tBox R).indicator g x - φ x‖ₑ ^ (2 : ℝ) := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ tBox R
          · simp only [Set.indicator_of_mem hx, le_refl]
          · simp [Set.indicator_of_notMem hx]
  have hstep2 : ∫⁻ x, ‖(tBox R).indicator g x - φ x‖ₑ ^ (2 : ℝ)
      ≤ (ENNReal.ofReal c) ^ (2 : ℝ) := lint_sq_le_of_eLpNorm hφapp
  have hstep3 : (ENNReal.ofReal c) ^ (2 : ℝ) = ENNReal.ofReal (c ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hc0.le (by norm_num), Real.rpow_two]
  exact lt_of_le_of_lt (hstep1.trans (hstep2.trans_eq hstep3))
    ((ENNReal.ofReal_lt_ofReal_iff hη).mpr hc2)

end UnforcedLeray.Short.PartIIIb.Concrete
