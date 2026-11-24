import UnforcedLeray.Short.PartI.Sub.PartI_S18_1

/-!
# `PartI:S18/1/2`: `a ↦ J_a G` is continuous for `G` continuous with compact support

Source `the November 2 reference manuscript`
lines 946-953.  Leaf `DilWCcCont` of `PartI_S18_1`.

Proof: `J_a G` is a.e. the function `dilWFun a g`.  The `L²_M` norm of the difference is
`eLpNorm` of `dilWFun a g - dilWFun a₀ g`, and its square is handled by dominated convergence:
for `a ∈ (a₀/2, 2a₀)` the integrand is bounded by `(2K)²` times the indicator of a fixed ball,
since `g` is bounded and supported in a fixed ball.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartI

theorem dilWCcCont : DilWCcCont := by
  intro M hM G hG a₀ ha₀
  obtain ⟨g, hgcont, hgc, hGg⟩ := hG
  have hloc : IsLocallyFiniteMeasure (Planar.wMeasure M) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure M))
  have hreg : (Planar.wMeasure M).Regular := inferInstance
  -- the representing family
  have hae : ∀ a : ℝ, (ha : 0 < a) →
      ⇑(Planar.dilW hM ha G) =ᵐ[Planar.wMeasure M] Planar.dilWFun a g := fun a ha =>
    (Planar.coeFn_dilW hM ha G).trans (Planar.dilWFun_congr ha hGg)
  -- support and bound of `g`
  obtain ⟨Cg, hCg⟩ := hgcont.bounded_above_of_compact_support hgc
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0)
  obtain ⟨R₁, hR₁0, hsupp⟩ : ∃ R₁ : ℝ, 0 ≤ R₁ ∧ ∀ z : ℂ, R₁ < ‖z‖ → g z = 0 := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨max R 0, le_max_right _ _, fun z hz => ?_⟩
    by_contra hne
    have h1 := hR (subset_tsupport g hne)
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : R ≤ max R 0 := le_max_left _ _
    linarith
  -- uniform bound for `a` near `a₀`
  have hA : ∀ a : ℝ, a₀ / 2 < a → ∀ y : ℂ, ‖Planar.dilWFun a g y‖ ≤ 4 / a₀ ^ 2 * Cg := by
    intro a ha y
    have ha0 : 0 < a := by linarith
    have hinv : (a ^ 2)⁻¹ ≤ 4 / a₀ ^ 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_self_lt_mul_self (by linarith : (0:ℝ) ≤ a₀ / 2) ha]
    unfold Planar.dilWFun
    rw [norm_mul, Complex.norm_of_nonneg (by positivity)]
    exact mul_le_mul hinv (hCg _) (norm_nonneg _) (by positivity)
  -- vanishing outside a fixed ball
  have hB : ∀ a : ℝ, 0 < a → a < 2 * a₀ → ∀ y : ℂ,
      R₁ * Real.sqrt (2 * a₀) < ‖y‖ → Planar.dilWFun a g y = 0 := by
    intro a ha0 ha2 y hy
    have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
    have hsS : Real.sqrt a ≤ Real.sqrt (2 * a₀) := Real.sqrt_le_sqrt ha2.le
    have h1 : R₁ * Real.sqrt a ≤ R₁ * Real.sqrt (2 * a₀) := mul_le_mul_of_nonneg_left hsS hR₁0
    have h2 : R₁ * Real.sqrt a < ‖y‖ := lt_of_le_of_lt h1 hy
    have h3 : R₁ < (Real.sqrt a)⁻¹ * ‖y‖ := by
      rw [← div_eq_inv_mul, lt_div_iff₀ hs]
      linarith
    unfold Planar.dilWFun
    have hz : g ((Real.sqrt a)⁻¹ • y) = 0 := by
      apply hsupp
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
      exact h3
    rw [hz, mul_zero]
  -- continuity in `a` at `a₀` for each point
  have hcont : ∀ a : ℝ, Continuous (fun y : ℂ => Planar.dilWFun a g y) := by
    intro a
    unfold Planar.dilWFun
    exact continuous_const.mul (hgcont.comp (continuous_const_smul _))
  have hpt : ∀ y : ℂ, ContinuousAt (fun a : ℝ => Planar.dilWFun a g y) a₀ := by
    intro y
    have h1 : ContinuousAt (fun a : ℝ => (a ^ 2)⁻¹) a₀ :=
      ContinuousAt.inv₀ (by fun_prop) (pow_ne_zero 2 ha₀.ne')
    have h2 : ContinuousAt (fun a : ℝ => (Real.sqrt a)⁻¹) a₀ :=
      ContinuousAt.inv₀ Real.continuous_sqrt.continuousAt (Real.sqrt_pos.2 ha₀).ne'
    unfold Planar.dilWFun
    refine ContinuousAt.mul (Complex.continuous_ofReal.continuousAt.comp h1) ?_
    exact hgcont.continuousAt.comp (h2.smul continuousAt_const)
  -- pointwise convergence of the squared integrand
  have hdiff : ∀ y : ℂ, Tendsto
      (fun a : ℝ => ‖Planar.dilWFun a g y - Planar.dilWFun a₀ g y‖ₑ ^ (2:ℝ)) (𝓝 a₀) (𝓝 0) := by
    intro y
    have h1 : Tendsto (fun a : ℝ => Planar.dilWFun a g y - Planar.dilWFun a₀ g y) (𝓝 a₀) (𝓝 0) := by
      have := (hpt y).tendsto.sub_const (Planar.dilWFun a₀ g y)
      rwa [sub_self] at this
    have h2 : Tendsto (fun a : ℝ => ‖Planar.dilWFun a g y - Planar.dilWFun a₀ g y‖ₑ) (𝓝 a₀) (𝓝 0) := by
      have := (continuous_enorm.tendsto (0 : ℂ)).comp h1
      simp only [Function.comp_def, enorm_zero] at this
      exact this
    have h3 := (ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto (0 : ℝ≥0∞) |>.comp h2
    simp only [Function.comp_def] at h3
    have h0 : (0 : ℝ≥0∞) ^ (2:ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    rw [h0] at h3
    exact h3
  -- measurability
  have hmeas : ∀ a : ℝ, Measurable (fun y : ℂ =>
      ‖Planar.dilWFun a g y - Planar.dilWFun a₀ g y‖ₑ ^ (2:ℝ)) := fun a =>
    (((hcont a).sub (hcont a₀)).enorm.measurable).pow_const _
  -- the dominating function
  have hnhds : Ioo (a₀ / 2) (2 * a₀) ∈ 𝓝 a₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hbound : ∀ a ∈ Ioo (a₀ / 2) (2 * a₀), ∀ y : ℂ,
      ‖Planar.dilWFun a g y - Planar.dilWFun a₀ g y‖ₑ ^ (2:ℝ) ≤
        (Metric.closedBall (0 : ℂ) (R₁ * Real.sqrt (2 * a₀))).indicator
          (fun _ => ENNReal.ofReal (2 * (4 / a₀ ^ 2 * Cg)) ^ (2:ℝ)) y := by
    intro a ha y
    by_cases hy : y ∈ Metric.closedBall (0 : ℂ) (R₁ * Real.sqrt (2 * a₀))
    · rw [Set.indicator_of_mem hy]
      have hzK : ‖Planar.dilWFun a g y - Planar.dilWFun a₀ g y‖ ≤ 2 * (4 / a₀ ^ 2 * Cg) := by
        have := hA a ha.1 y
        have := hA a₀ (by linarith) y
        calc _ ≤ ‖Planar.dilWFun a g y‖ + ‖Planar.dilWFun a₀ g y‖ := norm_sub_le _ _
          _ ≤ _ := by linarith
      have h1 : ‖Planar.dilWFun a g y - Planar.dilWFun a₀ g y‖ₑ ≤
          ENNReal.ofReal (2 * (4 / a₀ ^ 2 * Cg)) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hzK
      exact ENNReal.rpow_le_rpow h1 (by norm_num)
    · rw [Set.indicator_of_notMem hy]
      have hy' : R₁ * Real.sqrt (2 * a₀) < ‖y‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
      have z1 := hB a (by linarith [ha.1]) ha.2 y hy'
      have z2 := hB a₀ ha₀ (by linarith) y hy'
      simp [z1, z2, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
  -- the Lebesgue integral tends to zero
  have hint : Tendsto (fun a : ℝ => ∫⁻ y, ‖Planar.dilWFun a g y - Planar.dilWFun a₀ g y‖ₑ ^ (2:ℝ)
      ∂(Planar.wMeasure M)) (𝓝 a₀) (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence (μ := Planar.wMeasure M)
      ((Metric.closedBall (0 : ℂ) (R₁ * Real.sqrt (2 * a₀))).indicator
        (fun _ => ENNReal.ofReal (2 * (4 / a₀ ^ 2 * Cg)) ^ (2:ℝ)))
      (Eventually.of_forall (fun a => hmeas a))
      (by
        filter_upwards [hnhds] with a ha
        exact ae_of_all _ (fun y => hbound a ha y))
      (by
        rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
        exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
          measure_closedBall_lt_top.ne)
      (ae_of_all _ (fun y => hdiff y))
    rwa [lintegral_zero] at this
  -- the L² norm is the rpow of the integral
  have hform : ∀ a : ℝ, eLpNorm (Planar.dilWFun a g - Planar.dilWFun a₀ g) 2 (Planar.wMeasure M)
      = (∫⁻ y, ‖Planar.dilWFun a g y - Planar.dilWFun a₀ g y‖ₑ ^ (2:ℝ)
        ∂(Planar.wMeasure M)) ^ (1 / 2 : ℝ) := by
    intro a
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
  have hlim : Tendsto (fun a : ℝ =>
      eLpNorm (Planar.dilWFun a g - Planar.dilWFun a₀ g) 2 (Planar.wMeasure M)) (𝓝 a₀) (𝓝 0) := by
    have h4 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞) |>.comp hint
    simp only [Function.comp_def] at h4
    have h0 : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    rw [h0] at h4
    have hfun : (fun a : ℝ => eLpNorm (Planar.dilWFun a g - Planar.dilWFun a₀ g) 2
        (Planar.wMeasure M)) = fun a : ℝ => (∫⁻ y, ‖Planar.dilWFun a g y - Planar.dilWFun a₀ g y‖ₑ
          ^ (2:ℝ) ∂(Planar.wMeasure M)) ^ (1 / 2 : ℝ) := funext hform
    rw [hfun]
    exact h4
  -- transfer to `J_a G` in `L²_M`
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun a : Set.Ioi (0 : ℝ) =>
      ENNReal.toReal (eLpNorm (Planar.dilWFun a.1 g - Planar.dilWFun a₀ g) 2 (Planar.wMeasure M)))
      (𝓝 ⟨a₀, ha₀⟩) (𝓝 0) := by
    have h3 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (hlim.comp (continuous_subtype_val.tendsto (⟨a₀, ha₀⟩ : Set.Ioi (0:ℝ)))))
    simp only [Function.comp_def] at h3
    exact h3
  refine h2.congr (fun a => ?_)
  rw [Lp.norm_def]
  congr 1
  exact (eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans ((hae a.1 a.2).sub (hae a₀ ha₀)))).symm

end UnforcedLeray.Short.PartI
