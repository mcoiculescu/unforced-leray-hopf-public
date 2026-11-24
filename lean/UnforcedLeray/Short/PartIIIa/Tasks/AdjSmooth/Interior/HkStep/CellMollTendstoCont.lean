import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared

/-!
# `PartIII-a:T21/2/7/2/1/1/5/8`: mollification converges on continuous band-limited fields

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061.

A continuous `c`-periodic field `h` vanishing for `|x₂| > R` is uniformly continuous on the compact
set `K₂ = [-(c/2+1), c/2+1] × [-(R+2), R+2]`. For `‖y‖ < 1/(n+1)` and `x` in the band box
`[-c/2, c/2] × [-(R+1), R+1]`, the shifted points `x - y` and `x` lie in `K₂`, so
`|ρ_n ⋆ h - h| ≤ ε` there once `1/(n+1) < δ(ε)`. Off the box (inside the cell) the difference
vanishes. The weighted norm on the cell is then at most `ε` times a finite constant, the finite
measure of the box.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The compact set on which the mollified difference is controlled. -/
def mollK2 (c R : ℝ) : Set (ℝ × ℝ) :=
  Icc (-(c / 2 + 1)) (c / 2 + 1) ×ˢ Icc (-(R + 2)) (R + 2)

theorem isCompact_mollK2 (c R : ℝ) : IsCompact (mollK2 c R) :=
  isCompact_Icc.prod isCompact_Icc

theorem molKer_nonneg' (n : ℕ) (y : ℝ × ℝ) : 0 ≤ molKer n y :=
  (molBump n).nonneg_normed y

theorem molKer_integrable' (n : ℕ) : Integrable (molKer n) :=
  (molBump n).integrable_normed

theorem molKer_integral' (n : ℕ) : ∫ y, molKer n y = 1 :=
  (molBump n).integral_normed

theorem molKer_support' (n : ℕ) {y : ℝ × ℝ} (hy : molKer n y ≠ 0) :
    ‖y‖ < 1 / ((n : ℝ) + 1) := by
  have h : y ∈ Function.support (molKer n) := hy
  rw [molKer, ContDiffBump.support_normed_eq] at h
  exact mem_ball_zero_iff.1 h

theorem one_div_nat_succ_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_one (by positivity)]
  linarith

theorem cellMoll_eq_integral (n : ℕ) (h : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    cellMoll n h x = ∫ y, (molKer n y : ℂ) * h (x - y) := by
  simp only [cellMoll, cellConv, Complex.real_smul]

theorem cellMoll_sub_eq' (n : ℕ) {h : ℝ × ℝ → ℂ} (hcont : Continuous h) (x : ℝ × ℝ) :
    cellMoll n h x - h x = ∫ y, (molKer n y : ℂ) * (h (x - y) - h x) := by
  have hK : Integrable (fun y => (molKer n y : ℂ)) := (molKer_integrable' n).ofReal
  have hKh : Integrable (fun y => (molKer n y : ℂ) * h (x - y)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_ofReal.comp (molBump n).continuous_normed).mul
        (hcont.comp (continuous_const.sub continuous_id))
    · exact ((molBump n).hasCompactSupport_normed.comp_left Complex.ofReal_zero).mul_right
  have e2 : ∫ y, (molKer n y : ℂ) * h x = h x := by
    rw [integral_mul_const, integral_complex_ofReal, molKer_integral' n, Complex.ofReal_one,
      one_mul]
  have e3 : ∫ y, (molKer n y : ℂ) * (h (x - y) - h x) =
      (∫ y, (molKer n y : ℂ) * h (x - y)) - ∫ y, (molKer n y : ℂ) * h x := by
    rw [← integral_sub hKh (hK.mul_const (h x))]
    congr 1
    funext y
    ring
  rw [cellMoll_eq_integral, e3, e2]

/-- The mollified difference is small on the band box, once the mollifier radius is below `δ`. -/
theorem mollDiff_le_of_box {c R : ℝ} {h : ℝ × ℝ → ℂ} (hcont : Continuous h) {ε δ : ℝ}
    (hδ : ∀ x ∈ mollK2 c R, ∀ y ∈ mollK2 c R, dist x y < δ → dist (h x) (h y) < ε)
    (n : ℕ) (hn : 1 / ((n : ℝ) + 1) < δ) (x : ℝ × ℝ) (hx : x ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(R + 1)) (R + 1)) :
    ‖cellMoll n h x - h x‖ ≤ ε := by
  rw [cellMoll_sub_eq' n hcont x]
  have hbd : ∀ y : ℝ × ℝ, ‖(molKer n y : ℂ) * (h (x - y) - h x)‖ ≤ molKer n y * ε := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (molKer_nonneg' n y)]
    by_cases hy : molKer n y = 0
    · simp [hy]
    · have hy' := molKer_support' n hy
      have hy1 : ‖y‖ < 1 := lt_of_lt_of_le hy' (one_div_nat_succ_le_one n)
      have hd : dist (x - y) x < δ := by
        rw [dist_eq_norm, show x - y - x = -y by abel, norm_neg]
        exact lt_trans hy' hn
      have ha1 : ‖y.1‖ ≤ ‖y‖ := norm_fst_le y
      have ha2 : ‖y.2‖ ≤ ‖y‖ := norm_snd_le y
      rw [Real.norm_eq_abs] at ha1 ha2
      have hy1' := abs_le.1 (ha1.trans hy1.le)
      have hy2' := abs_le.1 (ha2.trans hy1.le)
      obtain ⟨⟨hx1a, hx1b⟩, ⟨hx2a, hx2b⟩⟩ := hx
      have hmem1 : x - y ∈ mollK2 c R := by
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
          simp only [Prod.fst_sub, Prod.snd_sub] <;> linarith [hy1'.1, hy1'.2, hy2'.1, hy2'.2]
      have hmem2 : x ∈ mollK2 c R := by
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
      have := hδ (x - y) hmem1 x hmem2 hd
      rw [dist_eq_norm] at this
      exact mul_le_mul_of_nonneg_left this.le (molKer_nonneg' n y)
  calc ‖∫ y, (molKer n y : ℂ) * (h (x - y) - h x)‖
      ≤ ∫ y, molKer n y * ε := norm_integral_le_of_norm_le ((molKer_integrable' n).mul_const ε)
        (Eventually.of_forall hbd)
    _ = ε := by rw [integral_mul_const, molKer_integral' n, one_mul]

/-- The mollified difference vanishes outside the band. -/
theorem mollDiff_zero_of_band {R : ℝ} {h : ℝ × ℝ → ℂ} (hR : ∀ x : ℝ × ℝ, R < |x.2| → h x = 0)
    (n : ℕ) (x : ℝ × ℝ) (hx : R + 1 < |x.2|) : cellMoll n h x - h x = 0 := by
  have hx0 : h x = 0 := hR x (by linarith)
  have hzero : ∀ y : ℝ × ℝ, (molKer n y : ℂ) * h (x - y) = 0 := by
    intro y
    by_cases hy : molKer n y = 0
    · simp [hy]
    · have hy' := molKer_support' n hy
      have hy1 : ‖y‖ < 1 := lt_of_lt_of_le hy' (one_div_nat_succ_le_one n)
      have ha2 : ‖y.2‖ ≤ ‖y‖ := norm_snd_le y
      rw [Real.norm_eq_abs] at ha2
      have hsub : |x.2| - |y.2| ≤ |(x - y).2| := by
        rw [Prod.snd_sub]
        exact abs_sub_abs_le_abs_sub _ _
      have : h (x - y) = 0 := hR (x - y) (by linarith [ha2.trans hy1.le, abs_le.1 (ha2.trans hy1.le)])
      rw [this, mul_zero]
  rw [cellMoll_eq_integral, hx0, sub_zero]
  simp [hzero]

/-- The finite constant: the cell-box has finite `cellMeasure`. -/
theorem cellMeasure_box_ne_top (c m R : ℝ) :
    B0579.cellMeasure c m (B0579.box c R) ≠ ⊤ := by
  rw [B0579.cellMeasure, withDensity_apply _ (B0579.isCompact_box c R).measurableSet]
  obtain ⟨C, hC⟩ := (B0579.isCompact_box c R).exists_bound_of_continuousOn
    (B0579.continuous_jb_rpow m).continuousOn
  have hle : ∫⁻ a in B0579.box c R, ((B0579.density m a : NNReal) : ℝ≥0∞)
      ∂(volume.restrict (B0579.cell c)) ≤
      ∫⁻ _ in B0579.box c R, ENNReal.ofReal C ∂(volume.restrict (B0579.cell c)) := by
    refine setLIntegral_mono' (B0579.isCompact_box c R).measurableSet (fun a ha => ?_)
    have h1 := hC a ha
    rw [Real.norm_eq_abs] at h1
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans h1)
  rw [setLIntegral_const] at hle
  refine ne_top_of_le_ne_top ?_ hle
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  rw [Measure.restrict_apply (B0579.isCompact_box c R).measurableSet]
  exact ne_top_of_le_ne_top (B0579.isCompact_box c R).measure_lt_top.ne
    (measure_mono inter_subset_left)

theorem cellMollTendstoCont : CellMollTendstoCont := by
  intro c m h hc hcont _hper hband
  obtain ⟨R, hR⟩ := hband
  set S := B0579.box c (R + 1) with hS
  have hSm : MeasurableSet S := (B0579.isCompact_box c (R + 1)).measurableSet
  set μ := B0579.cellMeasure c (-m) with hμ
  -- the finite constant
  have hBfin : (μ.restrict S) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact cellMeasure_box_ne_top c (-m) (R + 1)
  have hBc : (μ.restrict S) Set.univ ^ ((2 : ℝ≥0∞).toReal)⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin
  -- the key estimate
  have key : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      eLpNorm (cellMoll n h - h) 2 μ ≤ (μ.restrict S) Set.univ ^ ((2 : ℝ≥0∞).toReal)⁻¹ *
        ENNReal.ofReal η := by
    intro η hη
    have huc : UniformContinuousOn h (mollK2 c R) :=
      (isCompact_mollK2 c R).uniformContinuousOn_of_continuous hcont.continuousOn
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδpos
    refine ⟨N, fun n hn => ?_⟩
    have hn' : 1 / ((n : ℝ) + 1) < δ := by
      refine lt_of_le_of_lt ?_ hN
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    -- the integrand vanishes on the cell outside the box, so the norm lives on the box
    have hind : (cellMoll n h - h) =ᵐ[μ] S.indicator (cellMoll n h - h) := by
      have hcell : ∀ᵐ x ∂μ, x ∈ B0579.cell c :=
        (B0579.cellMeasure_ac c (-m)).ae_le (ae_restrict_mem (B0579.measurableSet_cell c))
      filter_upwards [hcell] with x hxc
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]
      · rw [Set.indicator_of_notMem hxS]
        have hx2 : R + 1 < |x.2| := by
          by_contra hcon
          apply hxS
          exact ⟨Ico_subset_Icc_self hxc.1, abs_le.1 (not_lt.1 hcon)⟩
        exact mollDiff_zero_of_band hR n x hx2
    have hfn : eLpNorm (cellMoll n h - h) 2 μ = eLpNorm (cellMoll n h - h) 2 (μ.restrict S) := by
      rw [eLpNorm_congr_ae hind, eLpNorm_indicator_eq_eLpNorm_restrict hSm]
    rw [hfn]
    refine eLpNorm_le_of_ae_bound (C := η) ?_
    refine (ae_restrict_iff' hSm).2 (Eventually.of_forall fun x hx => ?_)
    exact mollDiff_le_of_box hcont hδ n hn' x hx
  -- conclude the limit
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have hT0 : Tendsto (fun η : ℝ => ENNReal.ofReal η) (𝓝 0) (𝓝 0) := by
    have := ENNReal.continuous_ofReal.tendsto (0 : ℝ)
    simpa using this
  have hT : Tendsto (fun η : ℝ => (μ.restrict S) Set.univ ^ ((2 : ℝ≥0∞).toReal)⁻¹ *
      ENNReal.ofReal η) (𝓝 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hT0 (Or.inr hBc)
    simpa using this
  obtain ⟨η, hηpos, hηP⟩ := Metric.eventually_nhds_iff.1 (hT.eventually (gt_mem_nhds he))
  have hηhalf : (0 : ℝ) < η / 2 := by linarith
  have hlt : (μ.restrict S) Set.univ ^ ((2 : ℝ≥0∞).toReal)⁻¹ * ENNReal.ofReal (η / 2) < e := by
    apply hηP
    rw [Real.dist_eq, sub_zero, abs_of_pos hηhalf]
    linarith
  obtain ⟨N, hN⟩ := key (η / 2) hηhalf
  exact Filter.eventually_atTop.2 ⟨N, fun n hn => (hN n hn).trans hlt.le⟩

end UnforcedLeray.Short.IIIa
