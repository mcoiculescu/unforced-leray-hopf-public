import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayGradPerp.Bounds

/-!
# `measureH`-integrability of band-supported majorants (helper for `LerayGradPerp`)

For a continuous integrable `G ≥ 0` on `ℝ`, the function `p ↦ 1_{[s0,s1]}(p.1) G(p.2.2)` has
finite `measureH c`-lower integral of its `ofReal` (the `s`-weight is bounded on the band, the
`q`-range is the cell `(0, c]`, and the integral factorises over `s`, `q`, `η`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.GradPerpCut

theorem lintegral_band_mul_lt_top {c s0 s1 : ℝ} (hs0 : 0 < s0) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ η, 0 ≤ G η) (hGint : Integrable G) :
    ∫⁻ p : Chart, ENNReal.ofReal ((Icc s0 s1).indicator (fun _ => (1 : ℝ)) p.1 * G p.2.2)
      ∂(UnforcedLeray.B0220.measureH c) < ⊤ := by
  have hFm : Measurable fun p : Chart =>
      ENNReal.ofReal ((Icc s0 s1).indicator (fun _ => (1 : ℝ)) p.1 * G p.2.2) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_const.indicator measurableSet_Icc).comp measurable_fst).mul
        (hG.measurable.comp (measurable_snd.comp measurable_snd)))
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ≥0∞, A = fun s =>
      (Icc s0 s1).indicator (fun s => ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))) s := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ≥0∞, B = fun q => (Ioc 0 c).indicator (fun _ => (1 : ℝ≥0∞)) q :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ≥0∞, E = fun η => ENNReal.ofReal (G η) := ⟨_, rfl⟩
  have hAm : Measurable A := by
    rw [hA]
    exact Measurable.indicator (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
      measurableSet_Icc
  have hBm : Measurable B := by
    rw [hB]
    exact measurable_const.indicator measurableSet_Ioc
  have hEm : Measurable E := by
    rw [hE]
    exact ENNReal.measurable_ofReal.comp hG.measurable
  have hEfin : ∫⁻ η, E η < ⊤ := by
    rw [hE]
    exact hGint.lintegral_lt_top
  have hAfin : ∫⁻ s, A s < ⊤ := by
    have hApt : ∀ s : ℝ, A s ≤
        (Icc s0 s1).indicator (fun _ => ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ)))) s := by
      intro s
      rw [hA]
      by_cases hs : s ∈ Icc s0 s1
      · simp only [Set.indicator_of_mem hs]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs0 hs.1 (by norm_num))
      · simp [Set.indicator_of_notMem hs]
    refine lt_of_le_of_lt (lintegral_mono hApt) ?_
    rw [lintegral_indicator_const measurableSet_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hBfin : ∫⁻ q, B q < ⊤ := by
    simp only [hB]
    rw [lintegral_indicator_const measurableSet_Ioc, one_mul, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hfin : ∫⁻ p : Chart, A p.1 * (B p.2.1 * E p.2.2) < ⊤ := by
    have hvol3 : (volume : Measure (ℝ × (ℝ × ℝ))) =
        (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) := Measure.volume_eq_prod _ _
    have hvol2 : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) :=
      Measure.volume_eq_prod _ _
    have hg1 : Measurable fun y : ℝ × ℝ => B y.1 * E y.2 :=
      (hBm.comp measurable_fst).mul (hEm.comp measurable_snd)
    have step1 : ∫⁻ p : Chart, A p.1 * (B p.2.1 * E p.2.2) =
        (∫⁻ s, A s) * ∫⁻ y : ℝ × ℝ, B y.1 * E y.2 := by
      rw [hvol3]
      exact lintegral_prod_mul hAm.aemeasurable hg1.aemeasurable
    have step2 : ∫⁻ y : ℝ × ℝ, B y.1 * E y.2 = (∫⁻ q, B q) * ∫⁻ η, E η := by
      rw [hvol2]
      exact lintegral_prod_mul hBm.aemeasurable hEm.aemeasurable
    rw [step1, step2]
    exact ENNReal.mul_lt_top hAfin (ENNReal.mul_lt_top hBfin hEfin)
  rw [UnforcedLeray.B0220.measureH,
    lintegral_withDensity_eq_lintegral_mul _ UnforcedLeray.B0220.measurable_weightH hFm]
  rw [UnforcedLeray.B0220.cellMeasure,
    ← lintegral_indicator (UnforcedLeray.B0220.measurableSet_cell c)]
  refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hfin
  by_cases hp : p ∈ UnforcedLeray.B0220.cell c
  · have hq : p.2.1 ∈ Ioc 0 c := hp.2.1
    rw [Set.indicator_of_mem hp]
    by_cases hI : p.1 ∈ Icc s0 s1
    · simp only [Pi.mul_apply, UnforcedLeray.B0220.weightH, hA, hB, hE, Set.indicator_of_mem hI,
        Set.indicator_of_mem hq, one_mul, mul_one]
      exact le_rfl
    · simp [Pi.mul_apply, UnforcedLeray.B0220.weightH, hA, hB, hE, Set.indicator_of_notMem hI]
  · rw [Set.indicator_of_notMem hp]
    exact zero_le

/-- Squares of the error majorant are band-supported with an explicit profile. -/
theorem errFn_sq_eq {s0 s1 K : ℝ} (p : Chart) :
    errFn s0 s1 K p ^ 2 =
      (Icc s0 s1).indicator (fun _ => (1 : ℝ)) p.1 * (K ^ 2 * (1 + p.2.2 ^ 2)⁻¹) := by
  unfold errFn
  by_cases hI : p.1 ∈ Icc s0 s1
  · rw [Set.indicator_of_mem hI, Set.indicator_of_mem hI, one_mul]
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
  · simp [Set.indicator_of_notMem hI]

/-- The squared error majorant is `measureH c`-integrable. -/
theorem errFn_sq_integrable {c s0 s1 K : ℝ} (hs0 : 0 < s0) :
    Integrable (fun p : Chart => errFn s0 s1 K p ^ 2) (UnforcedLeray.B0220.measureH c) := by
  have hinv : Continuous fun η : ℝ => (1 + η ^ 2)⁻¹ :=
    (continuous_const.add (continuous_id.pow 2)).inv₀ (fun η => (by positivity : (0 : ℝ) < 1 + η ^ 2).ne')
  have hG : Continuous fun η : ℝ => K ^ 2 * (1 + η ^ 2)⁻¹ := continuous_const.mul hinv
  have hG0 : ∀ η : ℝ, 0 ≤ K ^ 2 * (1 + η ^ 2)⁻¹ := fun η => by positivity
  have hGint : Integrable fun η : ℝ => K ^ 2 * (1 + η ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul (K ^ 2)
  have hfun : (fun p : Chart => errFn s0 s1 K p ^ 2) =
      fun p : Chart => (Icc s0 s1).indicator (fun _ => (1 : ℝ)) p.1 * (K ^ 2 * (1 + p.2.2 ^ 2)⁻¹) := by
    funext p
    exact errFn_sq_eq p
  have hmeas : Measurable fun p : Chart => errFn s0 s1 K p ^ 2 := by
    rw [hfun]
    exact ((measurable_const.indicator measurableSet_Icc).comp measurable_fst).mul
      (hG.measurable.comp (measurable_snd.comp measurable_snd))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => sq_nonneg _)]
  simp_rw [errFn_sq_eq]
  exact lintegral_band_mul_lt_top hs0 (fun η : ℝ => K ^ 2 * (1 + η ^ 2)⁻¹) hG hG0 hGint

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.GradPerpCut
