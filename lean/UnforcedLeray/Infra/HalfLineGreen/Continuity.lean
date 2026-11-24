import UnforcedLeray.Infra.HalfLineGreen.Kernel

/-!
# Continuity of the half-line Green operator in the time variable

`paper/main.tex`, Section `sec:st18-329` (lines 419-436): the Green operator maps the space
`𝒳_β` of continuous functions into the space `𝒵_β` of continuous functions.

Hypotheses on the time dependence (`GreenKernel.TimeContinuous`):
* `τ ↦ K₋(τ, τ - r) x` is continuous for every fixed elapsed time `r > 0`;
* `τ ↦ K₊(τ, s) x` is continuous on `(-∞, s)` for every fixed `s`.

Both follow from joint strong continuity of the kernels off the diagonal
(`timeContinuous_of_jointly`), which is the form in which the manuscript's evolution provides
them ("jointly strongly continuous evolution", line 296). The first hypothesis is the one that
makes dominated convergence applicable to the singular past kernel: after the substitution
`s = τ - r`, the integrand `K₋(τ, τ-r) u(τ-r)` is dominated, uniformly for `τ` near `τ₁`, by the
integrable profile `C M e^{β τ₁ + |β|} (1 + r^{-1/2}) e^{-(β-β₋) r}`.

Main result: `continuousOn_green`, `τ ↦ (R u)(τ)` is continuous on `(-∞, τ₀]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Infra.HalfLineGreen

open UnforcedLeray.Infra.VolterraEvolution (continuousOn_clm_apply ae_ne_real)

/-- On `|τ - τ₁| < 1`, `e^{βτ} ≤ e^{βτ₁} e^{|β|}`. -/
theorem exp_mul_le_of_mem_Ioo {β τ τ₁ : ℝ} (hτ : τ ∈ Ioo (τ₁ - 1) (τ₁ + 1)) :
    Real.exp (β * τ) ≤ Real.exp (β * τ₁) * Real.exp |β| := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have habs : |τ - τ₁| ≤ 1 := (abs_sub_lt_iff.2 ⟨by linarith [hτ.2], by linarith [hτ.1]⟩).le
  have : β * (τ - τ₁) ≤ |β| :=
    calc β * (τ - τ₁) ≤ |β * (τ - τ₁)| := le_abs_self _
      _ = |β| * |τ - τ₁| := abs_mul _ _
      _ ≤ |β| * 1 := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ = |β| := mul_one _
  linarith

/-- Strong continuity in the integration variable follows from joint strong continuity of the
past kernel on `{s < τ}`. -/
theorem continuousOn_Km_of_jointly {𝕜 X Z : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] {Km : ℝ → ℝ → X →L[𝕜] Z}
    (hm : ∀ x, ContinuousOn (fun p : ℝ × ℝ => Km p.1 p.2 x) {p | p.2 < p.1}) (τ : ℝ) (x : X) :
    ContinuousOn (fun s => Km τ s x) (Iio τ) :=
  (hm x).comp (continuousOn_const.prodMk continuousOn_id) (fun _ hs => hs)

/-- Strong continuity in the integration variable follows from joint strong continuity of the
future kernel on `{τ ≤ s}`. -/
theorem continuousOn_Kp_of_jointly {𝕜 X Z : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] {Kp : ℝ → ℝ → X →L[𝕜] Z}
    (hp : ∀ x, ContinuousOn (fun p : ℝ × ℝ => Kp p.1 p.2 x) {p | p.1 ≤ p.2}) (τ : ℝ) (x : X) :
    ContinuousOn (fun s => Kp τ s x) (Ici τ) :=
  (hp x).comp (continuousOn_const.prodMk continuousOn_id) (fun _ hs => hs)

namespace GreenKernel

variable {𝕜 : Type*} [RCLike 𝕜] {X Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (K : GreenKernel 𝕜 X Z)

/-- Strong continuity of the kernels in the time variable `τ`:
`τ ↦ K₋(τ, τ - r) x` is continuous for each elapsed time `r > 0`, and `τ ↦ K₊(τ, s) x` is
continuous on `(-∞, s)`. -/
structure TimeContinuous : Prop where
  Km_shift : ∀ r, 0 < r → ∀ x, Continuous fun τ => K.Km τ (τ - r) x
  Kp : ∀ s x, ContinuousOn (fun τ => K.Kp τ s x) (Iio s)

/-- Joint strong continuity of the kernels off the diagonal gives `TimeContinuous`. -/
theorem timeContinuous_of_jointly
    (hm : ∀ x, ContinuousOn (fun p : ℝ × ℝ => K.Km p.1 p.2 x) {p | p.2 < p.1})
    (hp : ∀ x, ContinuousOn (fun p : ℝ × ℝ => K.Kp p.1 p.2 x) {p | p.1 ≤ p.2}) :
    K.TimeContinuous where
  Km_shift r hr x := by
    refine (hm x).comp_continuous (continuous_id.prodMk (continuous_id.sub continuous_const))
      (fun τ => ?_)
    show τ - r < τ
    linarith
  Kp s x := (hp x).comp (continuousOn_id.prodMk continuousOn_const)
    (fun τ (hτ : τ < s) => show τ ≤ s from le_of_lt hτ)

variable [NormedSpace ℝ Z]

/-- Continuity of the past part `τ ↦ ∫_{-∞}^τ K₋(τ,s) u(s) ds` on `(-∞, τ₀]`. -/
theorem continuousOn_pastIntegral (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β)
    {τ₀ M : ℝ} {u : ℝ → X} (hu : Continuous u) (hM : ∀ s ≤ τ₀, ‖u s‖ ≤ M * Real.exp (β * s)) :
    ContinuousOn (fun τ => ∫ s in Iio τ, K.Km τ s (u s)) (Iic τ₀) := by
  have hM0 : 0 ≤ M :=
    (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((norm_nonneg _).trans (hM τ₀ le_rfl))
  have ha : 0 < β - K.βm := sub_pos.2 hβm
  have hrw : (fun τ => ∫ s in Iio τ, K.Km τ s (u s)) =
      fun τ => ∫ r in Ioi (0 : ℝ), K.Km τ (τ - r) (u (τ - r)) := by
    funext τ
    exact setIntegral_Iio_eq_Ioi τ (fun s => K.Km τ s (u s))
  rw [hrw]
  intro τ₁ _
  refine continuousWithinAt_of_dominated
    (bound := fun r => K.C * M * (Real.exp (β * τ₁) * Real.exp |β|) * pastProfile (β - K.βm) r)
    ?_ ?_ ?_ ?_
  · -- measurability
    refine Eventually.of_forall (fun τ => ?_)
    have hc : ContinuousOn (fun r => K.Km τ (τ - r) (u (τ - r))) (Ioi 0) :=
      (K.continuousOn_Km_apply hu τ).comp (continuousOn_const.sub continuousOn_id)
        (fun r (hr : 0 < r) => show τ - r < τ by linarith)
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · -- domination
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioo_mem_nhds (sub_one_lt τ₁) (lt_add_one τ₁))] with τ hτ hτ₁
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
    have h1 := K.norm_Km_apply_le (β := β) (M := M) (show τ - r < τ by linarith)
      (hM (τ - r) (by linarith [mem_Iic.1 hτ]))
    rw [sub_sub_cancel] at h1
    refine h1.trans ?_
    have hp := pastProfile_nonneg (β - K.βm) hr.le
    have hCM : 0 ≤ K.C * M := mul_nonneg K.C_nonneg hM0
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exp_mul_le_of_mem_Ioo hτ₁) hCM) hp
  · -- integrable bound
    exact (integrableOn_pastProfile ha).const_mul _
  · -- pointwise continuity
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
    have hc : ContinuousOn (fun τ => K.Km τ (τ - r) (u (τ - r))) univ := by
      refine continuousOn_clm_apply (fun x => (hK.Km_shift r hr x).continuousOn)
        (fun τ _ => ⟨K.C * (1 + r ^ (-(1 / 2 : ℝ))) * Real.exp (K.βm * r), ?_⟩)
        (hu.comp (continuous_id.sub continuous_const)).continuousOn
      refine Eventually.of_forall (fun t => ?_)
      have := K.norm_Km_le t (t - r) (by linarith)
      rwa [sub_sub_cancel] at this
    exact (continuousOn_univ.1 hc).continuousWithinAt

/-- Continuity of the future part `τ ↦ ∫_τ^{τ₀} K₊(τ,s) u(s) ds` on `(-∞, τ₀]`. -/
theorem continuousOn_futureIntegral (hK : K.TimeContinuous) {β : ℝ} (hβp : β < K.βp)
    {τ₀ M : ℝ} {u : ℝ → X} (hu : Continuous u) (hM : ∀ s ≤ τ₀, ‖u s‖ ≤ M * Real.exp (β * s)) :
    ContinuousOn (fun τ => ∫ s in τ..τ₀, K.Kp τ s (u s)) (Iic τ₀) := by
  have hM0 : 0 ≤ M :=
    (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((norm_nonneg _).trans (hM τ₀ le_rfl))
  intro τ₁ hτ₁
  set a := τ₁ - 1
  set F : ℝ → ℝ → Z := fun τ s => (Ioi τ).indicator (fun s => K.Kp τ s (u s)) s with hF
  -- the interval integral as an integral over the fixed set `Ioc a τ₀`
  have heq : ∀ τ ∈ Ioc a τ₀, ∫ s in τ..τ₀, K.Kp τ s (u s) = ∫ s in Ioc a τ₀, F τ s := by
    intro τ hτ
    rw [intervalIntegral.integral_of_le hτ.2, hF, setIntegral_indicator measurableSet_Ioi,
      Ioc_inter_Ioi, max_eq_right hτ.1.le]
  have hcont : ContinuousWithinAt (fun τ => ∫ s in Ioc a τ₀, F τ s) (Iic τ₀) τ₁ := by
    refine continuousWithinAt_of_dominated
      (bound := fun _ => K.C * M * (Real.exp (β * τ₁) * Real.exp |β|)) ?_ ?_ ?_ ?_
    · -- measurability
      refine Eventually.of_forall (fun τ => ?_)
      rw [hF, aestronglyMeasurable_indicator_iff measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi]
      exact ((K.continuousOn_Kp_apply hu τ).mono
        (fun s hs => mem_Ici.2 (le_of_lt (mem_Ioi.1 hs.1)))).aestronglyMeasurable
        (measurableSet_Ioi.inter measurableSet_Ioc)
    · -- domination
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioo_mem_nhds (sub_one_lt τ₁) (lt_add_one τ₁))] with τ _ hτ₁'
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hB : 0 ≤ K.C * M * (Real.exp (β * τ₁) * Real.exp |β|) :=
        mul_nonneg (mul_nonneg K.C_nonneg hM0) (by positivity)
      by_cases hsτ : s ∈ Ioi τ
      · rw [hF]
        simp only
        rw [indicator_of_mem hsτ]
        refine (K.norm_Kp_apply_le' hβp (le_of_lt hsτ) (hM s hs.2) hM0).trans ?_
        exact mul_le_mul_of_nonneg_left (exp_mul_le_of_mem_Ioo hτ₁')
          (mul_nonneg K.C_nonneg hM0)
      · rw [hF]
        simp only
        rw [indicator_of_notMem hsτ, norm_zero]
        exact hB
    · -- integrable bound
      exact integrableOn_const measure_Ioc_lt_top.ne
    · -- pointwise continuity, off the single point `s = τ₁`
      filter_upwards [ae_restrict_of_ae (ae_ne_real τ₁)] with s hs
      rcases lt_or_gt_of_ne hs with hlt | hgt
      · -- `s < τ₁`: the integrand vanishes near `τ₁`
        refine (continuousAt_const (y := (0 : Z))).continuousWithinAt.congr_of_eventuallyEq ?_ ?_
        · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hlt)] with τ hτ
          rw [hF]
          simp only
          rw [indicator_of_notMem (fun h : s ∈ Ioi τ => lt_asymm (mem_Ioi.1 hτ) h)]
        · rw [hF]
          simp only
          rw [indicator_of_notMem (fun h : s ∈ Ioi τ₁ => lt_asymm hlt h)]
      · -- `s > τ₁`: the integrand is `K₊(τ,s) u(s)` near `τ₁`
        have hc : ContinuousAt (fun τ => K.Kp τ s (u s)) τ₁ :=
          (hK.Kp s (u s)).continuousAt (Iio_mem_nhds hgt)
        refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
        · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hgt)] with τ hτ
          rw [hF]
          simp only
          rw [indicator_of_mem (mem_Ioi.2 hτ)]
        · rw [hF]
          simp only
          rw [indicator_of_mem (mem_Ioi.2 hgt)]
  refine hcont.congr_of_eventuallyEq ?_ (heq τ₁ ⟨sub_one_lt τ₁, hτ₁⟩)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (sub_one_lt τ₁))] with τ hτ hτa
  exact heq τ ⟨hτa, hτ⟩

/-- **Continuity of the Green operator.** Under `TimeContinuous`, for `β₋ < β < β₊` and a
continuous `u` with `‖u s‖ ≤ M e^{βs}` on `(-∞, τ₀]`, the function `τ ↦ (R u)(τ)` is continuous
on `(-∞, τ₀]`. -/
theorem continuousOn_green (hK : K.TimeContinuous) {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp)
    {τ₀ M : ℝ} {u : ℝ → X} (hu : Continuous u) (hM : ∀ s ≤ τ₀, ‖u s‖ ≤ M * Real.exp (β * s)) :
    ContinuousOn (K.green τ₀ u) (Iic τ₀) :=
  (K.continuousOn_pastIntegral hK hβm hu hM).sub (K.continuousOn_futureIntegral hK hβp hu hM)

end GreenKernel

end UnforcedLeray.Infra.HalfLineGreen
