import UnforcedLeray.Loc.Hyp.BackgroundStrongForm.HeatPairing
import UnforcedLeray.Loc.Hyp.BackgroundStrongForm.GradientL2

/-!
# H-BgStrong, helpers: the heat profile solves its equation at every phase
(`HeatProfileEquation`)

Proof of `HeatProfileEquation` (`Loc/Hyp/BackgroundStrongForm/Hypotheses.lean`;
`paper/main.tex` lines 159–163, blueprint unit B0707): for every vector test `φ`,

  `d/dτ ∫⟨H_h[u](τ), φ⟩ = ∫⟨H_h[u](τ), hΔφ - φ - ½(y·∇)φ⟩`.

By `integral_heatProfile_inner`, `∫⟨H(τ), ψ⟩ = e^{-τ} J_ψ(e^{-τ/2})` with
`J_ψ(μ) = ∫⟨u(w), Ψ_ψ(μw)⟩ dw` and `Ψ_ψ = e^{hΔ}ψ`. `J_ψ` is differentiable for `μ > 0`
with `J'_ψ(μ) = ∫⟨u(w), DΨ_ψ(μw)w⟩` (`hasDerivAt_J`: differentiation under the integral sign;
`|u(w)||DΨ_ψ(μw)w| ≤ C sup|DΨ_ψ|(1 + μ|w|)^{-4}` uniformly near `μ`, since `|u(w)| ≤ C|w|⁻¹`), and
the dilation commutator `μDΨ_ψ(μw)w = Ψ_{(y·∇)ψ}(μw) - 2hΨ_{Δψ}(μw)` (`fderiv_kconv_self`)
turns `μJ'_ψ` into `J_{(y·∇)ψ} - 2hJ_{Δψ}`. The chain rule then gives
`d/dτ ∫⟨H, φ⟩ = -∫⟨H, φ⟩ - ½∫⟨H, (y·∇)φ⟩ + h∫⟨H, Δφ⟩`. Only the bound `|u(x)| ≤ C|x|⁻¹`
and the smoothness of `u` off `0` are used (the higher bounds enter through the compiled
`invDist_dil` and `heat_smoothing`, for continuity of `H(τ)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal

namespace UnforcedLeray.Blueprint.HypBg

open UnforcedLeray.HeatProfileReg (dil heatProfile_eq_average invDist_dil uniform_bound
  heat_smoothing InvDist)
open UnforcedLeray.Blueprint.L13 (radialDeriv isVectorTest_radialDeriv)

variable {h C : ℝ} {u : SpatialField}

/-- `1/(1 + μr)⁴ ≤ m⁻⁴/(1 + r)⁴` for `m = min 1 μ`. -/
theorem decay_scale {μ : ℝ} (hμ : 0 < μ) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (hmμ : m ≤ μ)
    {r : ℝ} (hr : 0 ≤ r) : 1 / (1 + μ * r) ^ 4 ≤ (m ^ 4)⁻¹ / (1 + r) ^ 4 := by
  have h1 : m * (1 + r) ≤ 1 + μ * r := by nlinarith
  have h2 : 0 < m * (1 + r) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc (1 + r) ^ 4 = (m ^ 4)⁻¹ * (m * (1 + r)) ^ 4 := by
        field_simp
    _ ≤ (m ^ 4)⁻¹ * (1 + μ * r) ^ 4 := by gcongr

/-- Pairings of `u` (`|u(x)| ≤ C|x|⁻¹`) with continuous fields decaying like `(1 + |w|)^{-4}`
converge. -/
theorem integrable_inner_decay (hum : Measurable u) (hu0 : ∀ x : Space, x ≠ 0 → ‖u x‖ ≤ C / ‖x‖)
    (hC0 : 0 ≤ C) {G : Space → Space} (hG : Continuous G) {M : ℝ} (hM0 : 0 ≤ M)
    (hGd : ∀ w, ‖G w‖ ≤ M / (1 + ‖w‖) ^ 4) :
    Integrable (fun w => inner ℝ (u w) (G w)) := by
  have hmeas : Measurable (fun w => inner ℝ (u w) (G w)) := hum.inner hG.measurable
  have hpt : ∀ w : Space, w ≠ 0 → ‖inner ℝ (u w) (G w)‖ ≤ C * M / ‖w‖ / (1 + ‖w‖) ^ 4 := by
    intro w hw
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    calc ‖inner ℝ (u w) (G w)‖ ≤ ‖u w‖ * ‖G w‖ := norm_inner_le_norm _ _
      _ ≤ (C / ‖w‖) * (M / (1 + ‖w‖) ^ 4) :=
          mul_le_mul (hu0 w hw) (hGd w) (norm_nonneg _) (div_nonneg hC0 hpos.le)
      _ = C * M / ‖w‖ / (1 + ‖w‖) ^ 4 := by ring
  rw [← Set.indicator_self_add_compl (Metric.ball (0 : Space) 1)
    (fun w => inner ℝ (u w) (G w))]
  refine Integrable.add ?_ ?_
  · refine UnforcedLeray.L09.integrable_of_rpow_bound
      (hmeas.aestronglyMeasurable.indicator Metric.isOpen_ball.measurableSet)
      (α := 1) (C := C * M) (R := 1) (by norm_num) (fun x hx => ?_) (fun x hx => ?_)
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [Real.rpow_neg_one]
      by_cases hb : x ∈ Metric.ball (0 : Space) 1
      · rw [Set.indicator_of_mem hb]
        refine (hpt x hx).trans ?_
        have h1 : 1 ≤ (1 + ‖x‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg x])
        calc C * M / ‖x‖ / (1 + ‖x‖) ^ 4 ≤ C * M / ‖x‖ :=
              div_le_self (div_nonneg (mul_nonneg hC0 hM0) hpos.le) h1
          _ = C * M * ‖x‖⁻¹ := by ring
      · rw [Set.indicator_of_notMem hb, norm_zero]
        positivity
    · rw [Set.indicator_of_notMem]
      simp only [Metric.mem_ball, dist_zero_right, not_lt]
      exact hx.le
  · have hw4 : Integrable (fun w : Space => ((1 + ‖w‖) ^ 4)⁻¹) :=
      memLp_one_iff_integrable.mp (memLp_weight' 4 1 (by norm_num) (by norm_num) (by norm_num))
    refine (hw4.const_mul (C * M)).mono'
      (hmeas.aestronglyMeasurable.indicator Metric.isOpen_ball.measurableSet.compl)
      (Eventually.of_forall fun x => ?_)
    by_cases hb : x ∈ (Metric.ball (0 : Space) 1)ᶜ
    · rw [Set.indicator_of_mem hb]
      have hx1 : 1 ≤ ‖x‖ := by simpa using hb
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hx1
        linarith
      refine (hpt x hx0).trans ?_
      have hp : 0 < (1 + ‖x‖) ^ 4 := by positivity
      rw [div_div, div_le_iff₀ (by positivity)]
      have hcm : 0 ≤ C * M := mul_nonneg hC0 hM0
      calc C * M = C * M * ((1 + ‖x‖) ^ 4)⁻¹ * (1 + ‖x‖) ^ 4 := by field_simp
        _ ≤ C * M * ((1 + ‖x‖) ^ 4)⁻¹ * (‖x‖ * (1 + ‖x‖) ^ 4) := by
            gcongr
            nlinarith
    · rw [Set.indicator_of_notMem hb, norm_zero]
      positivity

/-- `J_ψ(μ) = ∫⟨u(w), Ψ_ψ(μw)⟩ dw`. -/
def Jfun (h : ℝ) (u : SpatialField) (ψ : Space → Space) (μ : ℝ) : ℝ :=
  ∫ w, inner ℝ (u w) (kconv h ψ (μ • w))

theorem integrable_J (hh : 0 < h) (hum : Measurable u)
    (hu0 : ∀ x : Space, x ≠ 0 → ‖u x‖ ≤ C / ‖x‖) (hC0 : 0 ≤ C) {ψ : Space → Space}
    (hψ : IsVectorTest ψ) {μ : ℝ} (hμ : 0 < μ) :
    Integrable (fun w => inner ℝ (u w) (kconv h ψ (μ • w))) := by
  obtain ⟨M, hM0, hM⟩ := kconv_decay hh hψ 4
  set m := min 1 μ
  have hm0 : 0 < m := lt_min one_pos hμ
  refine integrable_inner_decay hum hu0 hC0 ((continuous_kconv hh hψ).comp
    (continuous_const_smul μ)) (M := M * (m ^ 4)⁻¹) (by positivity) fun w => ?_
  refine (hM (μ • w)).1.trans ?_
  rw [norm_smul, Real.norm_of_nonneg hμ.le]
  have hd := decay_scale hμ hm0 (min_le_left _ _) (min_le_right _ _) (norm_nonneg w)
  calc M / (1 + μ * ‖w‖) ^ 4 = M * (1 / (1 + μ * ‖w‖) ^ 4) := by ring
    _ ≤ M * ((m ^ 4)⁻¹ / (1 + ‖w‖) ^ 4) := mul_le_mul_of_nonneg_left hd hM0
    _ = M * (m ^ 4)⁻¹ / (1 + ‖w‖) ^ 4 := by ring

/-- The commutator, applied: `μ DΨ_ψ(μw) w = Ψ_{(y·∇)ψ}(μw) - 2h Ψ_{Δψ}(μw)`. -/
theorem fderiv_kconv_scaled (hh : 0 < h) {ψ : Space → Space} (hψ : IsVectorTest ψ) {μ : ℝ}
    (hμ : μ ≠ 0) (w : Space) :
    fderiv ℝ (kconv h ψ) (μ • w) w =
      μ⁻¹ • (kconv h (radialDeriv ψ) (μ • w) - (2 * h) • kconv h (testLaplacian ψ) (μ • w)) := by
  rw [← fderiv_kconv_self hh hψ (μ • w), map_smul, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- **Differentiation of `J_ψ`** under the integral sign. -/
theorem hasDerivAt_J (hh : 0 < h) (hum : Measurable u)
    (hu0 : ∀ x : Space, x ≠ 0 → ‖u x‖ ≤ C / ‖x‖) (hC0 : 0 ≤ C) {ψ : Space → Space}
    (hψ : IsVectorTest ψ) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    HasDerivAt (Jfun h u ψ)
      (∫ w, inner ℝ (u w) (fderiv ℝ (kconv h ψ) (μ₀ • w) w)) μ₀ := by
  obtain ⟨M, hM0, hM⟩ := kconv_decay hh hψ 4
  set m := min 1 (μ₀ / 2)
  have hm0 : 0 < m := lt_min one_pos (by positivity)
  have hball : ∀ μ ∈ Metric.ball μ₀ (μ₀ / 2), m ≤ μ ∧ 0 < μ := by
    intro μ hμ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hμ
    exact ⟨(min_le_right _ _).trans (by linarith), by linarith⟩
  have hR := isVectorTest_radialDeriv hψ
  have hL := isVectorTest_testLaplacian hψ
  have hcF' : Continuous fun w : Space => fderiv ℝ (kconv h ψ) (μ₀ • w) w := by
    have e : (fun w : Space => fderiv ℝ (kconv h ψ) (μ₀ • w) w) = fun w =>
        μ₀⁻¹ • (kconv h (radialDeriv ψ) (μ₀ • w) - (2 * h) • kconv h (testLaplacian ψ) (μ₀ • w)) :=
      funext fun w => fderiv_kconv_scaled hh hψ hμ₀.ne' w
    rw [e]
    exact (((continuous_kconv hh hR).comp (continuous_const_smul μ₀)).sub
      (((continuous_kconv hh hL).comp (continuous_const_smul μ₀)).const_smul (2 * h))).const_smul
      μ₀⁻¹
  have hw4 : Integrable (fun w : Space => ((1 + ‖w‖) ^ 4)⁻¹) :=
    memLp_one_iff_integrable.mp (memLp_weight' 4 1 (by norm_num) (by norm_num) (by norm_num))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun μ w => inner ℝ (u w) (kconv h ψ (μ • w)))
    (F' := fun μ w => inner ℝ (u w) (fderiv ℝ (kconv h ψ) (μ • w) w))
    (bound := fun w => C * M * (m ^ 4)⁻¹ * ((1 + ‖w‖) ^ 4)⁻¹)
    (Metric.ball_mem_nhds μ₀ (by positivity : 0 < μ₀ / 2))
    (Eventually.of_forall fun μ => (hum.inner ((continuous_kconv hh hψ).comp
      (continuous_const_smul μ)).measurable).aestronglyMeasurable)
    (integrable_J hh hum hu0 hC0 hψ hμ₀)
    ((hum.inner hcF'.measurable).aestronglyMeasurable)
    (Eventually.of_forall fun w μ hμ => ?_)
    (hw4.const_mul _)
    (Eventually.of_forall fun w μ _ => ?_)
  · exact key.2
  · -- the bound
    obtain ⟨hmμ, hμpos⟩ := hball μ hμ
    by_cases hw : w = 0
    · subst hw
      simp only [smul_zero, map_zero, inner_zero_right, norm_zero]
      positivity
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hd := decay_scale hμpos hm0 (min_le_left _ _) hmμ (norm_nonneg w)
    have hD := (hM (μ • w)).2
    rw [norm_smul, Real.norm_of_nonneg hμpos.le] at hD
    calc ‖inner ℝ (u w) (fderiv ℝ (kconv h ψ) (μ • w) w)‖
        ≤ ‖u w‖ * (‖fderiv ℝ (kconv h ψ) (μ • w)‖ * ‖w‖) :=
          (norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ (C / ‖w‖) * ((M / (1 + μ * ‖w‖) ^ 4) * ‖w‖) := by
          gcongr
          · exact hu0 w hw
      _ = C * M * (1 / (1 + μ * ‖w‖) ^ 4) := by
          field_simp
      _ ≤ C * M * ((m ^ 4)⁻¹ / (1 + ‖w‖) ^ 4) :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg hC0 hM0)
      _ = C * M * (m ^ 4)⁻¹ * ((1 + ‖w‖) ^ 4)⁻¹ := by ring
  · -- the derivative
    have h1 : HasDerivAt (fun μ : ℝ => μ • w) w μ := by
      simpa using (hasDerivAt_id μ).smul_const w
    have h2 := (hasFDerivAt_kconv hh hψ (μ • w)).comp_hasDerivAt μ h1
    rw [(hasFDerivAt_kconv hh hψ (μ • w)).fderiv]
    have h3 := (hasDerivAt_const μ (u w)).inner ℝ h2
    simpa using h3

theorem integrable_inner_cont {V : SpatialField} (hV : Continuous V) {φ : Space → Space}
    (hφ : IsVectorTest φ) : Integrable (fun x => inner ℝ (V x) (φ x)) := by
  refine (hV.inner hφ.smooth.continuous).integrable_of_hasCompactSupport ?_
  refine hφ.compact.mono' ?_
  intro x hx
  apply subset_tsupport
  intro h0
  apply hx
  simp [h0]

/-- **`HeatProfileEquation`** (tex lines 159–163, B0707): `∂_τH = hΔH + ½y·∇H + ½H` for the heat
profile `H = H_h[u]`, weakly in space at every phase. -/
theorem heatProfileEquation : HeatProfileEquation := by
  intro h period u hh _hperiod hsmooth _hdss hbounds φ hφ τ
  obtain ⟨C, hC0, hC⟩ := uniform_bound hbounds
  have hCu : ∀ k : ℕ, k ≤ 3 → ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k u x‖ ≤ C / ‖x‖ ^ (k + 1) := fun k hk => hC k (by omega)
  have hu0 : ∀ x : Space, x ≠ 0 → ‖u x‖ ≤ C / ‖x‖ := by
    intro x hx
    have h0 := hC 0 (by omega) x hx
    rwa [norm_iteratedFDeriv_zero, zero_add, pow_one] at h0
  have hum : Measurable u := measurable_of_continuousOn_compl_singleton 0 hsmooth.continuousOn
  have hR := isVectorTest_radialDeriv hφ
  have hL := isVectorTest_testLaplacian hφ
  -- the representation `∫⟨H(σ), ψ⟩ = e^{-σ} J_ψ(e^{-σ/2})`
  have hE : ∀ ψ : Space → Space, IsVectorTest ψ → ∀ σ : ℝ,
      ∫ y, inner ℝ (heatProfile h u σ y) (ψ y) =
        Real.exp (-σ) * Jfun h u ψ (Real.exp (-(σ / 2))) :=
    fun ψ hψ σ => integral_heatProfile_inner hh hsmooth hCu hψ σ
  -- continuity of `H(τ)`
  obtain ⟨Q, _hQ0, hQ⟩ := heat_smoothing hh
  have hHc : Continuous (heatProfile h u τ) := by
    rw [heatProfile_eq_average hh u τ]
    exact (hQ _ _ (invDist_dil hsmooth hCu τ)).1.continuous
  set μ := Real.exp (-(τ / 2)) with hμdef
  have hμ : 0 < μ := Real.exp_pos _
  have hJ := hasDerivAt_J hh hum hu0 hC0 hφ hμ
  have hμd : HasDerivAt (fun σ : ℝ => Real.exp (-(σ / 2))) (Real.exp (-(τ / 2)) * (-(1 / 2))) τ := by
    have h1 : HasDerivAt (fun σ : ℝ => -(σ / 2)) (-(1 / 2)) τ :=
      (hasDerivAt_mul_const (-(1 / 2) : ℝ)).congr_of_eventuallyEq
        (Eventually.of_forall fun σ => by ring)
    exact (Real.hasDerivAt_exp _).comp τ h1
  have hed : HasDerivAt (fun σ : ℝ => Real.exp (-σ)) (Real.exp (-τ) * (-1)) τ :=
    (Real.hasDerivAt_exp _).comp τ (hasDerivAt_neg τ)
  rw [← hμdef] at hμd
  have hprod := hed.mul (hJ.comp τ hμd)
  have hfun : (fun σ => ∫ y, inner ℝ (heatProfile h u σ y) (φ y)) =
      fun σ => Real.exp (-σ) * (Jfun h u φ ∘ fun σ => Real.exp (-(σ / 2))) σ :=
    funext fun σ => hE φ hφ σ
  rw [hfun]
  refine hprod.congr_deriv ?_
  -- `μ J'_φ(μ) = J_{(y·∇)φ}(μ) - 2h J_{Δφ}(μ)`
  have hJ' : μ * (∫ w, inner ℝ (u w) (fderiv ℝ (kconv h φ) (μ • w) w)) =
      Jfun h u (radialDeriv φ) μ - (2 * h) * Jfun h u (testLaplacian φ) μ := by
    rw [← integral_const_mul]
    have e : ∀ w, μ * inner ℝ (u w) (fderiv ℝ (kconv h φ) (μ • w) w) =
        inner ℝ (u w) (kconv h (radialDeriv φ) (μ • w)) -
          (2 * h) * inner ℝ (u w) (kconv h (testLaplacian φ) (μ • w)) := by
      intro w
      rw [fderiv_kconv_scaled hh hφ hμ.ne' w, inner_smul_right, inner_sub_right,
        inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul]
    simp only [e]
    rw [integral_sub (integrable_J hh hum hu0 hC0 hR hμ)
      ((integrable_J hh hum hu0 hC0 hL hμ).const_mul _), integral_const_mul]
    rfl
  -- the right side by linearity
  have hrhs : ∫ y, inner ℝ (heatProfile h u τ y) (adjointTest h φ y) =
      h * (∫ y, inner ℝ (heatProfile h u τ y) (testLaplacian φ y)) -
        (∫ y, inner ℝ (heatProfile h u τ y) (φ y)) -
          (1 / 2 : ℝ) * ∫ y, inner ℝ (heatProfile h u τ y) (radialDeriv φ y) := by
    have e : ∀ y, inner ℝ (heatProfile h u τ y) (adjointTest h φ y) =
        h * inner ℝ (heatProfile h u τ y) (testLaplacian φ y) -
          inner ℝ (heatProfile h u τ y) (φ y) -
            (1 / 2 : ℝ) * inner ℝ (heatProfile h u τ y) (radialDeriv φ y) := by
      intro y
      simp only [adjointTest, inner_sub_right, inner_smul_right]
    simp only [e]
    have i1 : Integrable (fun y => h * inner ℝ (heatProfile h u τ y) (testLaplacian φ y)) :=
      (integrable_inner_cont hHc hL).const_mul h
    have i2 : Integrable (fun y => inner ℝ (heatProfile h u τ y) (φ y)) :=
      integrable_inner_cont hHc hφ
    have i3 : Integrable (fun y => (1 / 2 : ℝ) * inner ℝ (heatProfile h u τ y) (radialDeriv φ y)) :=
      (integrable_inner_cont hHc hR).const_mul _
    have i12 : Integrable (fun y => h * inner ℝ (heatProfile h u τ y) (testLaplacian φ y) -
        inner ℝ (heatProfile h u τ y) (φ y)) := i1.sub i2
    rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul]
  rw [hrhs, hE _ hL τ, hE _ hφ τ, hE _ hR τ, ← hμdef]
  simp only [Function.comp_apply]
  rw [← hμdef]
  linear_combination (-(1 / 2) * Real.exp (-τ)) * hJ'

end UnforcedLeray.Blueprint.HypBg
