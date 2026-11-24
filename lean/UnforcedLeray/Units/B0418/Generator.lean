import UnforcedLeray.Units.B0418.HeatGen
import UnforcedLeray.Units.B0418.Semigroup

/-!
# B0418 helper: the generator `νΔ + ½ y·∇ + ½` of `S_ν` on smooth compactly supported fields

Blueprint unit B0418 (`paper/main.tex` lines 7412 and 7419--7420: "The spatial semigroup of
`νΔ + ½y·∇ + ½` is ...", "Differentiation verifies the generator, initially for smooth
functions"). For `h ∈ C_c^∞(ℝ³; ℝ³)` and `1 ≤ p < ∞` we prove
`r⁻¹ (S_ν(r)h - h) → νΔh + ½ y·∇h + ½ h` in `L^p` as `r → 0⁺`, i.e. `C_c^∞` lies in the
domain of the `L^p` generator, on which the generator is the stated operator.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.B0418

open UnforcedLeray.AncientLocalization

variable {p : ℝ≥0∞}

/-- The operator `νΔ + ½ y·∇ + ½` of tex line 7412, on differentiable fields:
`y·∇h(y) = Dh(y) y`. -/
def generator (ν : ℝ) (h : SpatialField) (y : Space) : Space :=
  ν • vecLaplacian h y + (1 / 2 : ℝ) • fderiv ℝ h y y + (1 / 2 : ℝ) • h y

/-- One-sided difference quotients at `0` of a function differentiable at `0`. -/
theorem tendsto_slope_right {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) :
    Tendsto (fun r => r⁻¹ * (f r - f 0)) (𝓝[>] 0) (𝓝 d) := by
  have h1 := (hasDerivAt_iff_tendsto_slope_zero.mp hf).mono_left
    (nhdsWithin_mono _ (fun x (hx : x ∈ Ioi (0 : ℝ)) =>
      Set.mem_compl_singleton_iff.mpr (ne_of_gt hx)))
  simpa using h1

theorem tendsto_exp_slope : Tendsto (fun r : ℝ => r⁻¹ * (Real.exp r - 1)) (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_slope_right (Real.hasDerivAt_exp 0)
  simpa using h

theorem tendsto_halfexp_slope :
    Tendsto (fun r : ℝ => r⁻¹ * (Real.exp (r / 2) - 1)) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hd : HasDerivAt (fun r : ℝ => Real.exp (r / 2)) (Real.exp (0 / 2) * (1 / 2)) 0 :=
    (Real.hasDerivAt_exp _).comp 0 ((hasDerivAt_id 0).div_const 2)
  have h := tendsto_slope_right hd
  simpa using h

/-- `r⁻¹ (h(e^{r/2} y) - h(y)) → ½ Dh(y) y` in `L^p`, for `h ∈ C_c^∞`. -/
theorem tendsto_dilation_generator (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞)) {h : SpatialField}
    (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Tendsto (fun r : ℝ => eLpNorm (fun y => r⁻¹ • (h (Real.exp (r / 2) • y) - h y) -
      (1 / 2 : ℝ) • fderiv ℝ h y y) p volume) (𝓝[>] 0) (𝓝 0) := by
  have hdiff : Differentiable ℝ h := (contDiff_one_of_infty hs).differentiable one_ne_zero
  have hcf : Continuous (fderiv ℝ h) := (contDiff_one_of_infty hs).continuous_fderiv one_ne_zero
  obtain ⟨L, hL⟩ := hcf.bounded_above_of_compact_support (hc.fderiv ℝ)
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Space)
  set L' := max L 0
  set R' := max R 0
  have hzero : ∀ y : Space, R < ‖y‖ → y ∉ tsupport h := by
    intro y hy hm
    have h1 := hR hm
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  have hlip : ∀ u v : Space, ‖h u - h v‖ ≤ L' * ‖u - v‖ := by
    intro u v
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff x)
      (fun x _ => (hL x).trans (le_max_left _ _)) (mem_univ v) (mem_univ u)
  have hp0 : p ≠ 0 := ne_zero_of_one_le hp1
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hb := tendsto_halfexp_slope
  have hbev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r⁻¹ * (Real.exp (r / 2) - 1) < 1 :=
    hb.eventually (gt_mem_nhds (by norm_num))
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have hlim : Tendsto (fun r : ℝ => ∫⁻ y, ‖r⁻¹ • (h (Real.exp (r / 2) • y) - h y) -
      (1 / 2 : ℝ) • fderiv ℝ h y y‖ₑ ^ p.toReal) (𝓝[>] 0) (𝓝 (∫⁻ _y : Space, (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      ((Metric.closedBall (0 : Space) R').indicator
        (fun _ => (ENNReal.ofReal (2 * L' * R')) ^ p.toReal)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall (fun r => ?_)
      have hA : Continuous (fun y : Space => h (Real.exp (r / 2) • y)) :=
        hs.continuous.comp (continuous_const_smul _)
      have hB : Continuous (fun y : Space => fderiv ℝ h y y) := hcf.clm_apply continuous_id
      have hh : Continuous h := hs.continuous
      have hc1 : Continuous (fun y : Space => r⁻¹ • (h (Real.exp (r / 2) • y) - h y) -
          (1 / 2 : ℝ) • fderiv ℝ h y y) := by
        have h1 : Continuous (fun y : Space => r⁻¹ • (h (Real.exp (r / 2) • y) - h y)) :=
          (hA.sub hh).const_smul r⁻¹
        have h2 : Continuous (fun y : Space => (1 / 2 : ℝ) • fderiv ℝ h y y) :=
          hB.const_smul (1 / 2 : ℝ)
        exact h1.sub h2
      exact hc1.enorm.measurable.pow_const _
    · filter_upwards [self_mem_nhdsWithin, hbev] with r hr hbr
      have hr0 : (0 : ℝ) < r := hr
      have hlam : 1 ≤ Real.exp (r / 2) := Real.one_le_exp (by linarith)
      refine Eventually.of_forall (fun y => ?_)
      by_cases hy : ‖y‖ ≤ R'
      · rw [Set.indicator_of_mem (by simpa using hy)]
        gcongr
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        have h1 : ‖r⁻¹ • (h (Real.exp (r / 2) • y) - h y)‖ ≤ L' * R' := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
          have h2 := hlip (Real.exp (r / 2) • y) y
          have h3 : ‖Real.exp (r / 2) • y - y‖ = (Real.exp (r / 2) - 1) * ‖y‖ := by
            rw [show Real.exp (r / 2) • y - y = (Real.exp (r / 2) - 1) • y by
              rw [sub_smul, one_smul], norm_smul, Real.norm_of_nonneg (by linarith)]
          rw [h3] at h2
          calc r⁻¹ * ‖h (Real.exp (r / 2) • y) - h y‖
              ≤ r⁻¹ * (L' * ((Real.exp (r / 2) - 1) * ‖y‖)) :=
                mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hr0.le)
            _ = L' * (r⁻¹ * (Real.exp (r / 2) - 1)) * ‖y‖ := by ring
            _ ≤ L' * 1 * R' :=
                mul_le_mul (mul_le_mul_of_nonneg_left hbr.le (le_max_right _ _)) hy
                  (norm_nonneg _) (by positivity)
            _ = L' * R' := by ring
        have h4 : ‖(1 / 2 : ℝ) • fderiv ℝ h y y‖ ≤ L' * R' := by
          rw [norm_smul]
          have h5 : ‖fderiv ℝ h y y‖ ≤ L' * R' :=
            ((fderiv ℝ h y).le_opNorm y).trans
              (mul_le_mul ((hL y).trans (le_max_left _ _)) hy (norm_nonneg _) (le_max_right _ _))
          have h6 : 0 ≤ L' * R' := mul_nonneg (le_max_right _ _) (le_max_right _ _)
          calc ‖(1 / 2 : ℝ)‖ * ‖fderiv ℝ h y y‖ ≤ 1 * (L' * R') := by
                gcongr
                norm_num
            _ = L' * R' := one_mul _
        calc ‖r⁻¹ • (h (Real.exp (r / 2) • y) - h y) - (1 / 2 : ℝ) • fderiv ℝ h y y‖
            ≤ ‖r⁻¹ • (h (Real.exp (r / 2) • y) - h y)‖ + ‖(1 / 2 : ℝ) • fderiv ℝ h y y‖ :=
              norm_sub_le _ _
          _ ≤ L' * R' + L' * R' := add_le_add h1 h4
          _ = 2 * L' * R' := by ring
      · rw [Set.indicator_of_notMem (by simpa using hy)]
        have hy' : R < ‖y‖ := lt_of_le_of_lt (le_max_left _ _) (not_le.mp hy)
        have hy0 : y ∉ tsupport h := hzero y hy'
        have hly : R < ‖Real.exp (r / 2) • y‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          calc R < ‖y‖ := hy'
            _ = 1 * ‖y‖ := (one_mul _).symm
            _ ≤ Real.exp (r / 2) * ‖y‖ := by gcongr
        rw [image_eq_zero_of_notMem_tsupport (hzero _ hly), image_eq_zero_of_notMem_tsupport hy0,
          fderiv_of_notMem_tsupport ℝ hy0]
        simp only [sub_self, smul_zero, ContinuousLinearMap.zero_apply, enorm_zero]
        rw [ENNReal.zero_rpow_of_pos hpr]
    · rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpr.le ENNReal.ofReal_ne_top)
        measure_closedBall_lt_top.ne
    · refine Eventually.of_forall (fun y => ?_)
      have hd1 : HasDerivAt (fun r : ℝ => Real.exp (r / 2) • y)
          ((Real.exp (0 / 2) * (1 / 2)) • y) 0 :=
        ((Real.hasDerivAt_exp _).comp 0 ((hasDerivAt_id 0).div_const 2)).smul_const y
      have hd2 := (hdiff (Real.exp (0 / 2) • y)).hasFDerivAt.comp_hasDerivAt 0 hd1
      have hd3 : HasDerivAt (fun r : ℝ => h (Real.exp (r / 2) • y))
          (fderiv ℝ h y ((1 / 2 : ℝ) • y)) 0 := by
        have e1 : Real.exp (0 / 2) • y = y := by simp
        have e2 : (Real.exp (0 / 2) * (1 / 2)) • y = (1 / 2 : ℝ) • y := by simp
        rw [e1, e2] at hd2
        exact hd2
      have hsl := (hasDerivAt_iff_tendsto_slope_zero.mp hd3).mono_left
        (nhdsWithin_mono _ (fun x (hx : x ∈ Ioi (0 : ℝ)) =>
          Set.mem_compl_singleton_iff.mpr (ne_of_gt hx)))
      have hsl' : Tendsto (fun r : ℝ => r⁻¹ • (h (Real.exp (r / 2) • y) - h y))
          (𝓝[>] 0) (𝓝 (fderiv ℝ h y ((1 / 2 : ℝ) • y))) := by
        simpa using hsl
      have h1 := hsl'.sub_const ((1 / 2 : ℝ) • fderiv ℝ h y y)
      rw [map_smul, sub_self] at h1
      have h2 := (continuous_enorm.tendsto (0 : Space)).comp h1
      rw [enorm_zero] at h2
      have h3 := ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp h2
      rw [ENNReal.zero_rpow_of_pos hpr] at h3
      exact h3
  rw [lintegral_zero] at hlim
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by positivity)] at h4

/-- Pointwise algebraic decomposition of the similarity difference quotient. -/
theorem quotient_decomposition {ν r : ℝ} (hr : r ≠ 0) (hτ : ν * (Real.exp r - 1) ≠ 0)
    (h : SpatialField) (y : Space) :
    r⁻¹ • (freeEvolution ν r h y - h y) - generator ν h y =
      (Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹) •
          ((ν * (Real.exp r - 1))⁻¹ •
            (Heat.flow h (ν * (Real.exp r - 1)) (Real.exp (r / 2) • y) -
              h (Real.exp (r / 2) • y)) - vecLaplacian h (Real.exp (r / 2) • y)) +
        (Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹) •
          (vecLaplacian h (Real.exp (r / 2) • y) - vecLaplacian h y) +
        (Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹ - ν) • vecLaplacian h y +
        (r⁻¹ * (Real.exp (r / 2) - 1)) • (h (Real.exp (r / 2) • y) - h y) +
        (r⁻¹ * (Real.exp (r / 2) - 1) - 1 / 2) • h y +
        (r⁻¹ • (h (Real.exp (r / 2) • y) - h y) - (1 / 2 : ℝ) • fderiv ℝ h y y) := by
  set τ := ν * (Real.exp r - 1) with hτdef
  set lam := Real.exp (r / 2) with hlam
  set a := lam * τ * r⁻¹ with ha
  have hk : a • (τ⁻¹ • (Heat.flow h τ (lam • y) - h (lam • y))) =
      (lam * r⁻¹) • (Heat.flow h τ (lam • y) - h (lam • y)) := by
    rw [smul_smul]
    congr 1
    rw [ha]
    field_simp
  rw [freeEvolution_apply, generator, smul_sub a (τ⁻¹ • _), hk]
  module

end UnforcedLeray.B0418
