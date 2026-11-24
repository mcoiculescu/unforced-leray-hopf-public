import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_2

/-!
# Part I, task `PartI:S11/1/2/1`: smooth compactly supported profiles are dense in `ProfL2 M`

Source: `the November 2 reference manuscript`, lines 841-889.
Plan: Mathlib density of `C_c^∞(ℝ)` in `L²(profileMeasure M)`, then cut off near `0` with
`Real.smoothTransition`; the removed part has norm `≤ C μ((0,δ])^{1/2} → 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartI.SmoothProfDenseAux

open UnforcedLeray UnforcedLeray.Planar

theorem mu_Iic_zero (M : ℝ) : profileMeasure M (Iic 0) = 0 := by
  unfold profileMeasure
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have : Iic (0:ℝ) ∩ Ioi 0 = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
    intro h; linarith [h.1, h.2]
  rw [this]; simp

theorem mu_Ioc_le {M : ℝ} (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) :
    profileMeasure M (Ioc 0 δ) ≤
      ENNReal.ofReal (2 * π * δ * (1 + δ ^ 2) ^ M) * ENNReal.ofReal δ := by
  unfold profileMeasure
  rw [withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 Ioc_subset_Ioi_self]
  calc ∫⁻ x in Ioc 0 δ, ENNReal.ofReal (2 * π * x * (1 + x ^ 2) ^ M)
      ≤ ∫⁻ _ in Ioc 0 δ, ENNReal.ofReal (2 * π * δ * (1 + δ ^ 2) ^ M) := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 : 0 < x := hx.1
        have hxδ : x ≤ δ := hx.2
        have h1 : (1 + x ^ 2) ^ M ≤ (1 + δ ^ 2) ^ M :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) hM.le
        have h2 : 0 ≤ (1 + x ^ 2) ^ M := by positivity
        have h3 : 0 ≤ (1 + δ ^ 2) ^ M := by positivity
        have h4 : 0 < π := Real.pi_pos
        calc 2 * π * x * (1 + x ^ 2) ^ M ≤ 2 * π * δ * (1 + x ^ 2) ^ M := by gcongr
          _ ≤ _ := by gcongr
    _ = _ := by rw [setLIntegral_const, Real.volume_Ioc]; simp

theorem mu_Iic_le {M : ℝ} (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) :
    profileMeasure M (Iic δ) ≤
      ENNReal.ofReal (2 * π * δ * (1 + δ ^ 2) ^ M) * ENNReal.ofReal δ := by
  have : Iic δ ⊆ Iic 0 ∪ Ioc 0 δ := by
    intro x hx
    by_cases h : x ≤ 0
    · exact Or.inl h
    · exact Or.inr ⟨not_le.1 h, hx⟩
  calc profileMeasure M (Iic δ) ≤ profileMeasure M (Iic 0 ∪ Ioc 0 δ) := measure_mono this
    _ ≤ profileMeasure M (Iic 0) + profileMeasure M (Ioc 0 δ) := measure_union_le _ _
    _ ≤ _ := by rw [mu_Iic_zero, zero_add]; exact mu_Ioc_le hM hδ

theorem finiteOnCompacts {M : ℝ} (hM : 0 < M) : IsFiniteMeasureOnCompacts (profileMeasure M) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.bddAbove
  have hsub : K ⊆ Iic (max R 1) := fun x hx => (hR hx).trans (le_max_left _ _)
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (mu_Iic_le hM (by positivity)) ?_)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem tendsto_mu_Iic {M : ℝ} (hM : 0 < M) :
    Tendsto (fun n : ℕ => profileMeasure M (Iic (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  have hanti : Antitone fun n : ℕ => Iic (1 / ((n : ℝ) + 1)) := by
    intro a b hab x hx
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact le_trans (mem_Iic.1 hx) (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hinter : ⋂ n : ℕ, Iic (1 / ((n : ℝ) + 1)) = Iic 0 := by
    ext x
    simp only [mem_iInter, mem_Iic]
    constructor
    · intro h
      exact ge_of_tendsto' (tendsto_one_div_add_atTop_nhds_zero_nat) h
    · intro h n
      exact h.trans (by positivity)
  have hfin : ∃ n : ℕ, profileMeasure M (Iic (1 / ((n : ℝ) + 1))) ≠ ⊤ := by
    refine ⟨0, ne_of_lt (lt_of_le_of_lt (mu_Iic_le hM (by norm_num)) ?_)⟩
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have := tendsto_measure_iInter_atTop (μ := profileMeasure M)
    (fun n => measurableSet_Iic.nullMeasurableSet) hanti hfin
  rwa [hinter, mu_Iic_zero] at this

/-- Cutting a smooth compactly supported function off near `0`. -/
theorem cutoff_approx {M : ℝ} (hM : 1 < M) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioi 0 ∧
      eLpNorm (g - ψ) 2 (profileMeasure M) ≤ ENNReal.ofReal ε := by
  have hM0 : 0 < M := by linarith
  obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h1 : Tendsto (fun n : ℕ => (profileMeasure M (Iic (1 / ((n : ℝ) + 1)))) ^ (1 / 2 : ℝ))
      atTop (𝓝 (0 ^ (1 / 2 : ℝ))) :=
    ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp (tendsto_mu_Iic hM0)
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
  have hlim := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) h1 (Or.inr enorm_ne_top)
  rw [mul_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  set χ : ℝ → ℝ := fun r => Real.smoothTransition (2 * r / δ - 1) with hχdef
  have hχ0 : ∀ r, r ≤ δ / 2 → χ r = 0 := by
    intro r hr
    apply Real.smoothTransition.zero_of_nonpos
    have : 2 * r / δ ≤ 1 := (div_le_one hδ).2 (by linarith)
    linarith
  have hχ1 : ∀ r, δ ≤ r → χ r = 1 := by
    intro r hr
    apply Real.smoothTransition.one_of_one_le
    have : 2 ≤ 2 * r / δ := (le_div_iff₀ hδ).2 (by linarith)
    linarith
  have hχs : ContDiff ℝ ∞ χ := by
    refine Real.smoothTransition.contDiff.comp ?_
    exact (((contDiff_const.mul contDiff_id).div_const δ).sub contDiff_const)
  refine ⟨fun r => ((χ r : ℝ) : ℂ) * g r, ?_, ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp hχs).mul hg
  · refine hc.mono ?_
    intro r hr
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hr ⊢
    exact hr.2
  · have hsub : Function.support (fun r => ((χ r : ℝ) : ℂ) * g r) ⊆ Ici (δ / 2) := by
      intro r hr
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hr
      by_contra h
      apply hr.1
      rw [hχ0 r (le_of_lt (not_le.1 h))]; simp
    refine (closure_minimal hsub isClosed_Ici).trans ?_
    intro x hx
    exact lt_of_lt_of_le (half_pos hδ) hx
  · calc eLpNorm (g - fun r => ((χ r : ℝ) : ℂ) * g r) 2 (profileMeasure M)
        ≤ eLpNorm ((Iic δ).indicator fun _ => C) 2 (profileMeasure M) := by
          refine eLpNorm_mono fun r => ?_
          have hdiff : (g - fun r => ((χ r : ℝ) : ℂ) * g r) r = ((1 - χ r : ℝ) : ℂ) * g r := by
            simp only [Pi.sub_apply]; push_cast; ring
          rw [hdiff]
          by_cases hr : r ≤ δ
          · rw [indicator_of_mem (mem_Iic.2 hr), Real.norm_of_nonneg hC0, norm_mul,
              Complex.norm_real]
            have h0 : 0 ≤ χ r := Real.smoothTransition.nonneg _
            have h1 : χ r ≤ 1 := Real.smoothTransition.le_one _
            rw [Real.norm_of_nonneg (by linarith)]
            calc (1 - χ r) * ‖g r‖ ≤ 1 * C := by
                  apply mul_le_mul (by linarith) (hC r) (norm_nonneg _) (by norm_num)
              _ = C := one_mul C
          · rw [hχ1 r (le_of_lt (not_le.1 hr))]
            simp
      _ = ‖C‖ₑ * (profileMeasure M (Iic δ)) ^ (1 / (2 : ℝ≥0∞).toReal) :=
          eLpNorm_indicator_const measurableSet_Iic (by norm_num) (by norm_num)
      _ ≤ ENNReal.ofReal ε := by
          have : (1 / (2 : ℝ≥0∞).toReal) = 1 / 2 := by simp
          rw [this]
          exact hn.le

end UnforcedLeray.Short.PartI.SmoothProfDenseAux

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar SmoothProfDenseAux

theorem smoothProfDense_proof : UnforcedLeray.Short.PartI.SmoothProfDense := by
  intro M hM
  have hM0 : 0 < M := by linarith
  have := finiteOnCompacts hM0
  have hT := Lp.dense_hasCompactSupport_contDiff (μ := profileMeasure M) (F := ℂ) (p := 2)
    (by norm_num)
  rw [Metric.dense_iff]
  intro f r hr
  obtain ⟨g', hg'ball, g, hg'g, hgc, hgs⟩ := Metric.dense_iff.1 hT f (r / 2) (half_pos hr)
  obtain ⟨ψ, hψs, hψc, hψt, hψn⟩ := cutoff_approx hM hgs hgc (ε := r / 4) (by positivity)
  have hmem : MemLp ψ 2 (profileMeasure M) := hψs.continuous.memLp_of_hasCompactSupport hψc
  have hd : dist g' (hmem.toLp ψ) ≤ r / 4 := by
    rw [Lp.dist_def]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) hψn
    filter_upwards [Lp.coeFn_sub g' (hmem.toLp ψ), hg'g, hmem.coeFn_toLp] with x h1 h2 h3
    simp [Pi.sub_apply, h2, h3]
  refine ⟨hmem.toLp ψ, ?_, ψ, hψs, hψc, hψt, hmem.coeFn_toLp⟩
  rw [Metric.mem_ball]
  have := dist_triangle f g' (hmem.toLp ψ)
  rw [Metric.mem_ball, dist_comm] at hg'ball
  rw [dist_comm]
  linarith

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.smoothProfDense_proof
