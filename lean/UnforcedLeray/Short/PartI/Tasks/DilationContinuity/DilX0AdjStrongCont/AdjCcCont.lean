import UnforcedLeray.Short.PartI.Sub.PartI_S18_2_1
import UnforcedLeray.Short.PartI.Tasks.DilationContinuity.DilX0AdjStrongCont.AdjFormula

/-!
# `PartI:S18/2/1/2`: `a ↦ (J_a)^* G` is continuous for `G` continuous with compact support

Source `the November 2 reference manuscript`
lines 946-953.  Leaf `DilWAdjCcCont` of `PartI_S18_2_1`.

Proof: by `dilWAdjFormula` the adjoint is a.e. `cand M a G`, and `cand M a g` is continuous in `z`
and in `a` (pointwise).  The `L²_M` distance is handled by dominated convergence, as for
`dilWCcCont`: for `a ∈ (a₀/2, 2a₀)` the integrand is bounded by a constant times the indicator of a
fixed ball.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartI

theorem dilWAdjCcCont : DilWAdjCcCont := by
  intro M hM G hG a₀ ha₀
  obtain ⟨g, hgcont, hgc, hGg⟩ := hG
  have hM0 : 0 ≤ M := by linarith
  have hloc : IsLocallyFiniteMeasure (Planar.wMeasure M) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure M))
  -- the adjoint is a.e. the explicit candidate built from the representative `g` of `G`
  have hae : ∀ b : ℝ, (hb : 0 < b) →
      ⇑(ContinuousLinearMap.adjoint (Planar.dilW hM hb) G) =ᵐ[Planar.wMeasure M] cand M b g := by
    intro b hb
    have hf := dilWAdjFormula M hM hb G
    have hsne : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb).ne'
    have hq := (Planar.qmp_smul_wMeasure (M := M) hsne).ae
      (p := fun y : ℂ => G y = g y) hGg
    filter_upwards [hf, hq] with z h1 h2
    simp only [h1, h2, cand, ratioR]
  -- continuity of the candidate in `z`
  have hcontz : ∀ b : ℝ, Continuous (cand M b g) := by
    intro b
    have hc : Continuous (fun z : ℂ => Real.sqrt b • z) := continuous_const_smul _
    have h1 : Continuous (fun z : ℂ => (1 + ‖Real.sqrt b • z‖ ^ 2) ^ M) :=
      (continuous_const.add ((hc.norm).pow 2)).rpow_const (fun _ => Or.inr hM0)
    have h2 : Continuous (fun z : ℂ => (1 + ‖z‖ ^ 2) ^ M) :=
      (continuous_const.add ((continuous_norm).pow 2)).rpow_const (fun _ => Or.inr hM0)
    have h3 : Continuous (fun z : ℂ =>
        (b⁻¹ * ((1 + ‖Real.sqrt b • z‖ ^ 2) ^ M / (1 + ‖z‖ ^ 2) ^ M) : ℝ)) :=
      continuous_const.mul (h1.div h2 (fun z => by positivity))
    unfold cand ratioR
    exact (Complex.continuous_ofReal.comp h3).mul (hgcont.comp hc)
  -- pointwise continuity in `b` at `a₀`
  have hpt : ∀ z : ℂ, ContinuousAt (fun b : ℝ => cand M b g z) a₀ := by
    intro z
    have hc : Continuous (fun b : ℝ => Real.sqrt b • z) := Real.continuous_sqrt.smul continuous_const
    have hr : Continuous (fun b : ℝ => (1 + ‖Real.sqrt b • z‖ ^ 2) ^ M) :=
      (continuous_const.add ((hc.norm).pow 2)).rpow_const (fun _ => Or.inr hM0)
    have h1 : ContinuousAt (fun b : ℝ => b⁻¹) a₀ := continuousAt_id.inv₀ ha₀.ne'
    have h2 : ContinuousAt (fun b : ℝ =>
        ((b⁻¹ * ((1 + ‖Real.sqrt b • z‖ ^ 2) ^ M / (1 + ‖z‖ ^ 2) ^ M) : ℝ) : ℂ)) a₀ :=
      Complex.continuous_ofReal.continuousAt.comp (h1.mul ((hr.div_const _).continuousAt))
    have h3 : ContinuousAt (fun b : ℝ => g (Real.sqrt b • z)) a₀ := (hgcont.comp hc).continuousAt
    unfold cand ratioR
    exact h2.mul h3
  -- the representative `g`: bound and support
  obtain ⟨Cg, hCg⟩ := hgcont.bounded_above_of_compact_support hgc
  obtain ⟨R₁, hR₁0, hsupp⟩ : ∃ R₁ : ℝ, 0 ≤ R₁ ∧ ∀ z : ℂ, R₁ < ‖z‖ → g z = 0 := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨max R 0, le_max_right _ _, fun z hz => ?_⟩
    by_contra hne
    have h1 := hR (subset_tsupport g hne)
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : R ≤ max R 0 := le_max_left _ _
    linarith
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 2 / a₀ * (max 1 (2 * a₀)) ^ M * Cg := ⟨_, rfl⟩
  -- uniform bound for `b` near `a₀`
  have hA : ∀ b : ℝ, a₀ / 2 < b → b < 2 * a₀ → ∀ y : ℂ, ‖cand M b g y‖ ≤ C₁ := by
    intro b hb1 hb2 y
    rw [hC₁]
    have hb0 : 0 < b := by linarith
    unfold cand
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hb0.le) (ratioR_nonneg M b y))]
    have hinv : b⁻¹ ≤ 2 / a₀ := by
      rw [inv_eq_one_div, div_le_div_iff₀ hb0 ha₀]
      linarith
    have hr : ratioR M b y ≤ (max 1 (2 * a₀)) ^ M :=
      (ratioR_le M hM0 hb0 y).trans
        (Real.rpow_le_rpow (le_max_of_le_left zero_le_one) (max_le_max le_rfl hb2.le) hM0)
    exact mul_le_mul (mul_le_mul hinv hr (ratioR_nonneg M b y) (by positivity))
      (hCg _) (norm_nonneg _) (by positivity)
  -- vanishing outside a fixed ball
  have hB : ∀ b : ℝ, a₀ / 2 < b → ∀ y : ℂ,
      R₁ / Real.sqrt (a₀ / 2) < ‖y‖ → cand M b g y = 0 := by
    intro b hb y hy
    have ht : 0 < Real.sqrt (a₀ / 2) := Real.sqrt_pos.2 (by linarith)
    have htb : Real.sqrt (a₀ / 2) ≤ Real.sqrt b := Real.sqrt_le_sqrt hb.le
    have hR : R₁ < ‖y‖ * Real.sqrt (a₀ / 2) := (div_lt_iff₀ ht).1 hy
    have h2 : R₁ < ‖Real.sqrt b • y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg b)]
      calc R₁ < ‖y‖ * Real.sqrt (a₀ / 2) := hR
        _ ≤ ‖y‖ * Real.sqrt b := mul_le_mul_of_nonneg_left htb (norm_nonneg y)
        _ = Real.sqrt b * ‖y‖ := mul_comm _ _
    unfold cand
    rw [hsupp _ h2, mul_zero]
  have hmeas : ∀ b : ℝ, Measurable (fun y : ℂ =>
      ‖cand M b g y - cand M a₀ g y‖ₑ ^ (2:ℝ)) := fun b =>
    (((hcontz b).sub (hcontz a₀)).enorm.measurable).pow_const _
  have hdiff : ∀ y : ℂ, Tendsto
      (fun b : ℝ => ‖cand M b g y - cand M a₀ g y‖ₑ ^ (2:ℝ)) (𝓝 a₀) (𝓝 0) := by
    intro y
    have h1 : Tendsto (fun b : ℝ => cand M b g y - cand M a₀ g y) (𝓝 a₀) (𝓝 0) := by
      have := (hpt y).tendsto.sub_const (cand M a₀ g y)
      rwa [sub_self] at this
    have h2 : Tendsto (fun b : ℝ => ‖cand M b g y - cand M a₀ g y‖ₑ) (𝓝 a₀) (𝓝 0) := by
      have := (continuous_enorm.tendsto (0 : ℂ)).comp h1
      simp only [Function.comp_def, enorm_zero] at this
      exact this
    have h3 := (ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto (0 : ℝ≥0∞) |>.comp h2
    simp only [Function.comp_def] at h3
    have h0 : (0 : ℝ≥0∞) ^ (2:ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    rw [h0] at h3
    exact h3
  have hnhds : Ioo (a₀ / 2) (2 * a₀) ∈ 𝓝 a₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hbound : ∀ b ∈ Ioo (a₀ / 2) (2 * a₀), ∀ y : ℂ,
      ‖cand M b g y - cand M a₀ g y‖ₑ ^ (2:ℝ) ≤
        (Metric.closedBall (0 : ℂ) (R₁ / Real.sqrt (a₀ / 2))).indicator
          (fun _ => ENNReal.ofReal (2 * C₁) ^ (2:ℝ)) y := by
    intro b hb y
    by_cases hy : y ∈ Metric.closedBall (0 : ℂ) (R₁ / Real.sqrt (a₀ / 2))
    · rw [Set.indicator_of_mem hy]
      have hzK : ‖cand M b g y - cand M a₀ g y‖ ≤ 2 * C₁ := by
        have h1 := hA b hb.1 hb.2 y
        have h2 := hA a₀ (by linarith) (by linarith) y
        calc _ ≤ ‖cand M b g y‖ + ‖cand M a₀ g y‖ := norm_sub_le _ _
          _ ≤ _ := by linarith
      have h1 : ‖cand M b g y - cand M a₀ g y‖ₑ ≤ ENNReal.ofReal (2 * C₁) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hzK
      exact ENNReal.rpow_le_rpow h1 (by norm_num)
    · rw [Set.indicator_of_notMem hy]
      have hy' : R₁ / Real.sqrt (a₀ / 2) < ‖y‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
      have z1 := hB b hb.1 y hy'
      have z2 := hB a₀ (by linarith) y hy'
      simp [z1, z2, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
  -- the Lebesgue integral tends to zero
  have hint : Tendsto (fun b : ℝ => ∫⁻ y, ‖cand M b g y - cand M a₀ g y‖ₑ ^ (2:ℝ)
      ∂(Planar.wMeasure M)) (𝓝 a₀) (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence (μ := Planar.wMeasure M)
      ((Metric.closedBall (0 : ℂ) (R₁ / Real.sqrt (a₀ / 2))).indicator
        (fun _ => ENNReal.ofReal (2 * C₁) ^ (2:ℝ)))
      (Eventually.of_forall (fun b => hmeas b))
      (by
        filter_upwards [hnhds] with b hb
        exact ae_of_all _ (fun y => hbound b hb y))
      (by
        rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
        exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
          measure_closedBall_lt_top.ne)
      (ae_of_all _ (fun y => hdiff y))
    rwa [lintegral_zero] at this
  -- the L² norm is the rpow of the integral
  have hform : ∀ a : ℝ, eLpNorm (cand M a g - cand M a₀ g) 2 (Planar.wMeasure M)
      = (∫⁻ y, ‖cand M a g y - cand M a₀ g y‖ₑ ^ (2:ℝ)
        ∂(Planar.wMeasure M)) ^ (1 / 2 : ℝ) := by
    intro a
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
  have hlim : Tendsto (fun a : ℝ =>
      eLpNorm (cand M a g - cand M a₀ g) 2 (Planar.wMeasure M)) (𝓝 a₀) (𝓝 0) := by
    have h4 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞) |>.comp hint
    simp only [Function.comp_def] at h4
    have h0 : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    rw [h0] at h4
    have hfun : (fun a : ℝ => eLpNorm (cand M a g - cand M a₀ g) 2 (Planar.wMeasure M)) =
        fun a : ℝ => (∫⁻ y, ‖cand M a g y - cand M a₀ g y‖ₑ
          ^ (2:ℝ) ∂(Planar.wMeasure M)) ^ (1 / 2 : ℝ) := funext hform
    rw [hfun]
    exact h4
  -- transfer to `(J_a)^* G` in `L²_M`
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun a : Set.Ioi (0 : ℝ) =>
      ENNReal.toReal (eLpNorm (cand M a.1 g - cand M a₀ g) 2 (Planar.wMeasure M)))
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
