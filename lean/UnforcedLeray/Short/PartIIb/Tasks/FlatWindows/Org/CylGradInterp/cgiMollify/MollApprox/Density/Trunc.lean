import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5_7_1

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

theorem cylMeas_eq_strip_smul' (c : ℝ) :
    cylMeas c = ENNReal.ofReal c⁻¹ • (volume : Measure Coord).restrict (moStrip c) := by
  unfold cylMeas UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ moStrip
  rw [Measure.prod_smul_right]
  congr 1
  have h1 : (volume : Measure ℝ).prod ((volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c))
      = ((volume : Measure ℝ).restrict univ).prod ((volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c)) := by
    rw [Measure.restrict_univ]
  rw [h1, Measure.prod_restrict]
  rfl

theorem cylMeas_ac_volume (c : ℝ) : cylMeas c ≪ (volume : Measure Coord) := by
  rw [cylMeas_eq_strip_smul' c]
  exact Measure.AbsolutelyContinuous.smul_left
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) _

theorem mollTrunc_proof : UnforcedLeray.Short.IIb.MollTrunc := by
  intro c r hc hr f hf hfin δ hδ
  have hr0 : 0 < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr0).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hr' : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  have hfin' : ∫⁻ x, ‖f x‖ₑ ^ r ∂(cylMeas c) ≠ ⊤ := by
    have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt).mp hfin
    rw [hr'] at this
    exact this.ne
  have hE : ∀ M : ℝ, eLpNorm (fun x => f x - (moBox M).indicator f x) (ENNReal.ofReal r) (cylMeas c)
      = (∫⁻ x, (moBox M)ᶜ.indicator (fun x => ‖f x‖ₑ ^ r) x ∂(cylMeas c)) ^ (1 / r) := by
    intro M
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hr']
    congr 2
    funext x
    by_cases hx : x ∈ moBox M
    · rw [Set.indicator_of_mem hx, sub_self, Set.indicator_of_notMem (show x ∉ (moBox M)ᶜ from fun h => h hx)]
      simp [ENNReal.zero_rpow_of_pos hr0]
    · rw [Set.indicator_of_notMem hx, sub_zero, Set.indicator_of_mem (show x ∈ (moBox M)ᶜ from hx)]
  have hlim : Tendsto (fun M : ℝ => ∫⁻ x, (moBox M)ᶜ.indicator (fun x => ‖f x‖ₑ ^ r) x ∂(cylMeas c))
      atTop (𝓝 0) := by
    have hmeasF : ∀ M : ℝ, AEMeasurable ((moBox M)ᶜ.indicator (fun x => ‖f x‖ₑ ^ r)) (cylMeas c) := by
      intro M
      exact ((hf.enorm.pow_const r).mono_ac (cylMeas_ac_volume c)).indicator
        (measurableSet_moBox M).compl
    have := tendsto_lintegral_filter_of_dominated_convergence' (μ := cylMeas c)
      (l := atTop) (F := fun M x => (moBox M)ᶜ.indicator (fun x => ‖f x‖ₑ ^ r) x)
      (f := fun _ => 0) (fun x => ‖f x‖ₑ ^ r)
      (Eventually.of_forall fun M => hmeasF M)
      (Eventually.of_forall fun M => ae_of_all _ fun x => Set.indicator_le_self _ _ x) hfin'
      (ae_of_all _ fun x => ?_)
    · simpa using this
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (max |x.1| |x.2.2|)] with M hM
      have hx : x ∈ moBox M := (mem_moBox M x).2
        ⟨le_trans (le_max_left _ _) hM, le_trans (le_max_right _ _) hM⟩
      simp [Set.indicator_of_notMem (show x ∉ (moBox M)ᶜ from fun h => h hx)]
  have hT : Tendsto (fun M : ℝ => eLpNorm (fun x => f x - (moBox M).indicator f x)
      (ENNReal.ofReal r) (cylMeas c)) atTop (𝓝 0) := by
    rw [show (fun M : ℝ => eLpNorm (fun x => f x - (moBox M).indicator f x)
        (ENNReal.ofReal r) (cylMeas c)) = fun M : ℝ =>
        (∫⁻ x, (moBox M)ᶜ.indicator (fun x => ‖f x‖ₑ ^ r) x ∂(cylMeas c)) ^ (1 / r) from funext hE]
    have h0 : (0 : ℝ≥0∞) ^ (1 / r) = 0 := ENNReal.zero_rpow_of_pos (by positivity)
    have hc' := ((ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0).comp hlim
    rw [h0] at hc'
    exact hc'
  exact ((tendsto_order.1 hT).2 δ hδ).exists

end UnforcedLeray.Short.IIb

end
