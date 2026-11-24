import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_3_2

/-!
# `CcTranslateL2`: continuity of translation for compactly supported continuous `φ`

Source `the November 2 reference manuscript`
lines 1556-1583. `φ` is uniformly continuous (Heine-Cantor with compact support). For `‖z‖ < 1`,
the integrand `‖φ(x-z) - φ x‖ₑ²` vanishes outside `T = cthickening 1 (tsupport φ)`, which is
compact, and is bounded there by `e²` where `e` is the uniform-continuity modulus.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ccTranslateL2 : CcTranslateL2 := by
  intro φ hc hs ε hε
  set T : Set (ℝ × Space) := Metric.cthickening 1 (tsupport φ) with hT_def
  have hTc : IsCompact T := hs.isCompact.cthickening
  have hTm : MeasurableSet T := hTc.isClosed.measurableSet
  have hTfin : volume T < ⊤ := hTc.measure_lt_top
  set V : ℝ := (volume T).toReal with hV_def
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVT : volume T = ENNReal.ofReal V := (ENNReal.ofReal_toReal hTfin.ne).symm
  have hVp : (0 : ℝ) < V + 1 := by linarith
  set e : ℝ := Real.sqrt (ε / (V + 1)) with he_def
  have he0 : 0 < e := Real.sqrt_pos.mpr (div_pos hε hVp)
  have he2 : e ^ 2 = ε / (V + 1) := Real.sq_sqrt (div_nonneg hε.le hVp.le)
  have hUC : UniformContinuous φ := hs.uniformContinuous_of_continuous hc
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuous_iff.mp hUC e he0
  refine ⟨min δ 1, lt_min hδ one_pos, fun z hz => ?_⟩
  have hzδ : ‖z‖ < δ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hz (min_le_right _ _)
  have hdn : ∀ x : ℝ × Space, ‖φ (x - z) - φ x‖ < e := by
    intro x
    have hd : dist (x - z) x < δ := by
      rw [dist_eq_norm, show x - z - x = -z by abel, norm_neg]
      exact hzδ
    have h := hunif hd
    rwa [dist_eq_norm] at h
  have hpt : ∀ x : ℝ × Space,
      ‖φ (x - z) - φ x‖ₑ ^ (2 : ℝ) ≤ T.indicator (fun _ => ENNReal.ofReal (e ^ 2)) x := by
    intro x
    by_cases hx : x ∈ T
    · have hdn' := (hdn x).le
      rw [indicator_of_mem hx, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
      apply ENNReal.ofReal_le_ofReal
      gcongr
    · rw [indicator_of_notMem hx]
      have h1 : φ (x - z) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        apply hx
        exact Metric.mem_cthickening_of_dist_le x (x - z) 1 (tsupport φ) hmem
          (by rw [dist_eq_norm, sub_sub_cancel]; exact hz1.le)
      have hxs : x ∉ tsupport φ := fun hxs =>
        hx (Metric.mem_cthickening_of_dist_le x x 1 (tsupport φ) hxs (by simp))
      have h2 : φ x = 0 := image_eq_zero_of_notMem_tsupport hxs
      simp [h1, h2]
  calc ∫⁻ x, ‖φ (x - z) - φ x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x, T.indicator (fun _ => ENNReal.ofReal (e ^ 2)) x := lintegral_mono hpt
    _ = ENNReal.ofReal (e ^ 2) * volume T := lintegral_indicator_const hTm _
    _ = ENNReal.ofReal (e ^ 2 * V) := by rw [hVT, ENNReal.ofReal_mul (sq_nonneg e)]
    _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε, he2, div_mul_eq_mul_div, div_lt_iff₀ hVp]
        nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
