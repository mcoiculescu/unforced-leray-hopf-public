import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

/-- The compact boxes inside the open strip `(-c/2, c/2) × ℝ`. -/
def cddBox (c : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  Icc (-(c / 2) + 1 / ((n : ℝ) + 2)) (c / 2 - 1 / ((n : ℝ) + 2)) ×ˢ Icc (-(n : ℝ)) n

theorem isCompact_cddBox (c : ℝ) (n : ℕ) : IsCompact (cddBox c n) :=
  isCompact_Icc.prod isCompact_Icc

theorem cddBox_closed (c : ℝ) (n : ℕ) : MeasurableSet (cddBox c n) :=
  (isCompact_cddBox c n).measurableSet

theorem cddBox_subset {c : ℝ} (n : ℕ) {x : ℝ × ℝ} (hx : x ∈ cddBox c n) :
    -(c / 2) < x.1 ∧ x.1 < c / 2 := by
  have h : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  exact ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩

theorem eventually_mem_cddBox {c : ℝ} {x : ℝ × ℝ} (h1 : -(c / 2) < x.1) (h2 : x.1 < c / 2) :
    ∀ᶠ n : ℕ in atTop, x ∈ cddBox c n := by
  obtain ⟨N1, hN1⟩ := exists_nat_one_div_lt (show 0 < min (x.1 + c / 2) (c / 2 - x.1) by
    apply lt_min <;> linarith)
  obtain ⟨N2, hN2⟩ := exists_nat_ge |x.2|
  filter_upwards [eventually_ge_atTop (max N1 N2)] with n hn
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : (N2 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hle : 1 / ((n : ℝ) + 2) ≤ 1 / ((N1 : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (N1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have hm1 := min_le_left (x.1 + c / 2) (c / 2 - x.1)
  have hm2 := min_le_right (x.1 + c / 2) (c / 2 - x.1)
  have ha := abs_le.1 (hN2.trans hn2)
  exact ⟨⟨by linarith, by linarith⟩, ⟨ha.1, ha.2⟩⟩

/-- Truncation of an `X_{-m,c}` field to the boxes converges. -/
theorem tendsto_truncate {c m : ℝ} {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    Tendsto (fun n : ℕ => eLpNorm (f - (cddBox c n).indicator f) 2 (B0579.cellMeasure c m)) atTop
      (𝓝 0) := by
  have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
  have hfin : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c m) ≠ ∞ := by
    have := hf.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2] at this
    have h3 := this.ne
    intro hcon
    apply h3
    rw [hcon]
    simp
  have hmeas : AEMeasurable (fun x => ‖f x‖ₑ ^ (2 : ℝ)) (B0579.cellMeasure c m) :=
    (hf.1.enorm : AEMeasurable _ _).pow_const _
  have key : Tendsto (fun n : ℕ => ∫⁻ x, ‖(f - (cddBox c n).indicator f) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure c m)) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := B0579.cellMeasure c m)
      (F := fun (n : ℕ) x => ‖(f - (cddBox c n).indicator f) x‖ₑ ^ (2 : ℝ))
      (f := fun _ => (0 : ℝ≥0∞)) (bound := fun x => ‖f x‖ₑ ^ (2 : ℝ))
      (fun n => ?_) ?_ hfin ?_
    · simpa using this
    · exact (((hf.1.sub ((hf.1.indicator (cddBox_closed c n)))).enorm : AEMeasurable _ _)).pow_const _
    · intro n
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ cddBox c n <;> simp [hx]
    · have hae : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), x.1 ≠ -(c / 2) := by
        have : (volume : Measure (ℝ × ℝ)) {x | ¬ x.1 ≠ -(c / 2)} = 0 := by
          have e : {x : ℝ × ℝ | ¬ x.1 ≠ -(c / 2)} = {-(c / 2)} ×ˢ (univ : Set ℝ) := by
            ext x; simp
          rw [e, Measure.volume_eq_prod, Measure.prod_prod]
          simp
        exact this
      have hae2 : ∀ᵐ x ∂(B0579.cellMeasure c m), x.1 ≠ -(c / 2) ∧ x ∈ B0579.cell c :=
        (B0579.cellMeasure_ac c m).ae_le
          ((ae_restrict_of_ae hae).and (ae_restrict_mem (B0579.measurableSet_cell c)))
      filter_upwards [hae2] with x hx
      have hx1 : -(c / 2) < x.1 := lt_of_le_of_ne hx.2.1.1 (Ne.symm hx.1)
      have hev := eventually_mem_cddBox hx1 hx.2.1.2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      simp [hn]
  have hcont := ((ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0).comp key
  have h0 : (0 : ℝ≥0∞) ^ ((1 : ℝ) / 2) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  rw [h0] at hcont
  refine hcont.congr fun n => ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2]
  simp

end UnforcedLeray.Short.IIIa
