import UnforcedLeray.Loc.Hyp.BackgroundStrongForm.TestSmoothing
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# H-BgStrong, helpers: the heat profile tested against a test, as a pairing of `u_dss`

Support for `Loc/Hyp/BackgroundStrongForm/HeatEquation.lean` (proof of
`HeatProfileEquation`, `paper/main.tex` lines 159–163, blueprint unit B0707).

For a field `b` continuous off `0` with `|b(x)||x| ≤ C` and a vector test `ψ`,
`∫⟨e^{hΔ}b, ψ⟩ = ∫⟨b, e^{hΔ}ψ⟩` (`integral_average_inner`; Fubini, justified by splitting `b`
into its integrable part on the unit ball and a bounded part, as in
`Loc/L13PhysicalRemainder/HeatSolenoidal.lean`). With `H_h[u](·, τ) = e^{hΔ}u_τ`,
`u_τ(x) = e^{τ/2}u(e^{τ/2}x)` (`heatProfile_eq_average`, from
`Loc/Hyp/HeatProfileRegularity/Scaling.lean`) and the substitution `w = e^{τ/2}x`:

  `∫⟨H_h[u](y, τ), ψ(y)⟩ dy = e^{-τ} ∫⟨u(w), Ψ_ψ(e^{-τ/2}w)⟩ dw`   (`integral_heatProfile_inner`),

so every phase derivative falls on the smooth, rapidly decaying `Ψ_ψ = e^{hΔ}ψ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal

namespace UnforcedLeray.Blueprint.HypBg

open UnforcedLeray.HeatProfileReg (dil heatProfile_eq_average invDist_dil InvDist)

section Split

variable {b : SpatialField} {C : ℝ}

theorem const_nonneg_of_bound (hC : ∀ x : Space, x ≠ 0 → ‖b x‖ * ‖x‖ ≤ C) : 0 ≤ C := by
  have h := hC (EuclideanSpace.single 0 1) (by simp)
  exact le_trans (by positivity) h

/-- The part of `b` on the unit ball is integrable. -/
theorem integrable_ballPart (hm : Measurable b) (hC : ∀ x : Space, x ≠ 0 → ‖b x‖ * ‖x‖ ≤ C) :
    Integrable ((Metric.ball (0 : Space) 1).indicator b) := by
  have hC0 := const_nonneg_of_bound hC
  refine UnforcedLeray.L09.integrable_of_rpow_bound
    (hm.aestronglyMeasurable.indicator Metric.isOpen_ball.measurableSet)
    (α := 1) (C := C) (R := 1) (by norm_num) (fun x hx => ?_) (fun x hx => ?_)
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hpos]
    by_cases hb : x ∈ Metric.ball (0 : Space) 1
    · rw [Set.indicator_of_mem hb]
      exact hC x hx
    · rw [Set.indicator_of_notMem hb]
      simpa using hC0
  · rw [Set.indicator_of_notMem]
    simp only [Metric.mem_ball, dist_zero_right, not_lt]
    exact hx.le

/-- `|b| ≤ |b 1_{B₁}| + C`. -/
theorem norm_le_ballPart_add (hC : ∀ x : Space, x ≠ 0 → ‖b x‖ * ‖x‖ ≤ C) (x : Space) :
    ‖b x‖ ≤ ‖(Metric.ball (0 : Space) 1).indicator b x‖ + C := by
  by_cases hb : x ∈ Metric.ball (0 : Space) 1
  · rw [Set.indicator_of_mem hb]
    linarith [const_nonneg_of_bound hC]
  · have hx1 : 1 ≤ ‖x‖ := by simpa using hb
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx1
      linarith
    have h1 := hC x hx0
    have h2 : ‖b x‖ ≤ C := by nlinarith [norm_nonneg (b x)]
    linarith [norm_nonneg ((Metric.ball (0 : Space) 1).indicator b x)]

end Split

variable {h : ℝ} {b : SpatialField} {C : ℝ} {ψ : Space → Space}

theorem kernel_neg (h : ℝ) (z : Space) : Heat.kernel h (-z) = Heat.kernel h z := by
  change Heat.Gaussian.kernel (4 * h) (-z) = Heat.Gaussian.kernel (4 * h) z
  simp [Heat.Gaussian.kernel, norm_neg]

/-- The Fubini integrand `K_h(y - x)⟨b(x), ψ(y)⟩` is integrable on `ℝ³ × ℝ³`. -/
theorem integrable_pairing_prod (hh : 0 < h) (hcont : ContinuousOn b {0}ᶜ)
    (hC : ∀ x : Space, x ≠ 0 → ‖b x‖ * ‖x‖ ≤ C) (hψ : IsVectorTest ψ) :
    Integrable (fun p : Space × Space => Heat.kernel h (p.1 - p.2) * inner ℝ (b p.2) (ψ p.1))
      ((volume : Measure Space).prod volume) := by
  have hC0 := const_nonneg_of_bound hC
  have hbm : Measurable b := measurable_of_continuousOn_compl_singleton 0 hcont
  have hK : Continuous (Heat.kernel h) := (Heat.Gaussian.kernel_smooth (4 * h)).continuous
  set Km := Heat.Gaussian.normalization (4 * h)
  have hKmax : ∀ z, Heat.kernel h z ≤ Km :=
    fun z => Heat.Gaussian.kernel_le_normalization (by positivity) z
  have hK0 : ∀ z, 0 ≤ Heat.kernel h z := fun z => Heat.kernel_nonneg hh z
  set b₁ := (Metric.ball (0 : Space) 1).indicator b
  have hb₁ : Integrable b₁ := integrable_ballPart hbm hC
  have hψn : Integrable (fun y => ‖ψ y‖) :=
    (hψ.smooth.continuous.norm).integrable_of_hasCompactSupport hψ.compact.norm
  have hmeas : AEStronglyMeasurable (fun p : Space × Space =>
      Heat.kernel h (p.1 - p.2) * inner ℝ (b p.2) (ψ p.1))
      ((volume : Measure Space).prod volume) :=
    ((hK.measurable.comp (measurable_fst.sub measurable_snd)).mul
      ((hbm.comp measurable_snd).inner
        (hψ.smooth.continuous.measurable.comp measurable_fst))).aestronglyMeasurable
  have hD₁ : Integrable (fun p : Space × Space => Km * (‖ψ p.1‖ * ‖b₁ p.2‖))
      ((volume : Measure Space).prod volume) :=
    (hψn.mul_prod hb₁.norm).const_mul Km
  have hD₂ : Integrable (fun p : Space × Space => C * (‖ψ p.1‖ * Heat.kernel h (p.1 - p.2)))
      ((volume : Measure Space).prod volume) := by
    refine Integrable.const_mul ?_ C
    have hm : AEStronglyMeasurable (fun p : Space × Space => ‖ψ p.1‖ * Heat.kernel h (p.1 - p.2))
        ((volume : Measure Space).prod volume) :=
      ((hψ.smooth.continuous.norm.measurable.comp measurable_fst).mul
        (hK.measurable.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · show Integrable (fun x => ‖ψ y‖ * Heat.kernel h (y - x))
      exact ((Heat.kernel_integrable hh).comp_sub_left y).const_mul _
    · show Integrable (fun y => ∫ x, ‖‖ψ y‖ * Heat.kernel h (y - x)‖)
      have he : (fun y => ∫ x, ‖‖ψ y‖ * Heat.kernel h (y - x)‖) =
          fun y => ‖ψ y‖ * ∫ x, Heat.kernel h x := by
        funext y
        have hn : ∀ x, ‖‖ψ y‖ * Heat.kernel h (y - x)‖ = ‖ψ y‖ * Heat.kernel h (y - x) :=
          fun x => Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hK0 _))
        simp only [hn]
        rw [integral_const_mul, integral_sub_left_eq_self (fun x => Heat.kernel h x) volume y]
      rw [he]
      exact hψn.mul_const _
  refine (hD₁.add hD₂).mono' hmeas (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK0 _)]
  have hi := abs_real_inner_le_norm (b p.2) (ψ p.1)
  have hs := norm_le_ballPart_add hC p.2
  calc Heat.kernel h (p.1 - p.2) * |inner ℝ (b p.2) (ψ p.1)|
      ≤ Heat.kernel h (p.1 - p.2) * (‖b p.2‖ * ‖ψ p.1‖) :=
        mul_le_mul_of_nonneg_left hi (hK0 _)
    _ ≤ Heat.kernel h (p.1 - p.2) * ((‖b₁ p.2‖ + C) * ‖ψ p.1‖) := by
        gcongr
        · exact hK0 _
    _ = Heat.kernel h (p.1 - p.2) * (‖ψ p.1‖ * ‖b₁ p.2‖) +
          C * (‖ψ p.1‖ * Heat.kernel h (p.1 - p.2)) := by ring
    _ ≤ Km * (‖ψ p.1‖ * ‖b₁ p.2‖) + C * (‖ψ p.1‖ * Heat.kernel h (p.1 - p.2)) := by
        gcongr
        exact hKmax _

/-- **Self-adjointness of the heat flow** against a test: `∫⟨e^{hΔ}b, ψ⟩ = ∫⟨b, e^{hΔ}ψ⟩`. -/
theorem integral_average_inner (hh : 0 < h) (hcont : ContinuousOn b {0}ᶜ)
    (hC : ∀ x : Space, x ≠ 0 → ‖b x‖ * ‖x‖ ≤ C) (hψ : IsVectorTest ψ) :
    ∫ y, inner ℝ (Heat.average h b y) (ψ y) = ∫ x, inner ℝ (b x) (kconv h ψ x) := by
  have hG := integrable_pairing_prod hh hcont hC hψ
  have h1 : ∀ y, inner ℝ (Heat.average h b y) (ψ y) =
      ∫ x, Heat.kernel h (y - x) * inner ℝ (b x) (ψ y) := by
    intro y
    have hint : Integrable (fun z : Space => Heat.kernel h z • b (y - z)) :=
      heat_integrable_of_inverse_bound hcont hC hh y
    have hav : Heat.average h b y = ∫ x, Heat.kernel h (y - x) • b x := by
      unfold Heat.average
      rw [← integral_sub_left_eq_self (fun z => Heat.kernel h z • b (y - z)) volume y]
      simp only [sub_sub_cancel]
    have hint' : Integrable (fun x : Space => Heat.kernel h (y - x) • b x) := by
      have := hint.comp_sub_left y
      simpa only [sub_sub_cancel] using this
    rw [hav, real_inner_comm, ← integral_inner hint']
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [inner_smul_right, real_inner_comm]
  have h2 : ∀ x, ∫ y, Heat.kernel h (y - x) * inner ℝ (b x) (ψ y) =
      inner ℝ (b x) (kconv h ψ x) := by
    intro x
    obtain ⟨B, hB⟩ := vtest_bound hψ
    have hint : Integrable (fun z : Space => Heat.kernel h z • ψ (x - z)) :=
      integrable_kconv_integrand hh hψ.smooth.continuous hB x
    have hk : kconv h ψ x = ∫ y, Heat.kernel h (y - x) • ψ y := by
      unfold kconv
      rw [← integral_sub_left_eq_self (fun y => Heat.kernel h (y - x) • ψ y) volume x]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      rw [show x - z - x = -z by abel, kernel_neg]
    have hint' : Integrable (fun y : Space => Heat.kernel h (y - x) • ψ y) := by
      have := hint.comp_sub_left x
      refine this.congr (Eventually.of_forall fun y => ?_)
      simp only
      rw [sub_sub_cancel, show x - y = -(y - x) by abel, kernel_neg]
    rw [hk, ← integral_inner hint']
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [inner_smul_right]
  simp only [h1]
  rw [integral_integral_swap hG]
  simp only [h2]

/-- **The heat profile tested against `ψ`** (lines 159–163):
`∫⟨H_h[u](y, τ), ψ(y)⟩ dy = e^{-τ} ∫⟨u(w), Ψ_ψ(e^{-τ/2}w)⟩ dw`. -/
theorem integral_heatProfile_inner (hh : 0 < h) {u : SpatialField}
    (hu : ContDiffOn ℝ ∞ u {0}ᶜ)
    (hCu : ∀ k : ℕ, k ≤ 3 → ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ k u x‖ ≤ C / ‖x‖ ^ (k + 1))
    (hψ : IsVectorTest ψ) (τ : ℝ) :
    ∫ y, inner ℝ (heatProfile h u τ y) (ψ y) =
      Real.exp (-τ) * ∫ w, inner ℝ (u w) (kconv h ψ (Real.exp (-(τ / 2)) • w)) := by
  have hinv : InvDist (dil τ u) C := invDist_dil hu hCu τ
  have hb : ∀ x : Space, x ≠ 0 → ‖dil τ u x‖ * ‖x‖ ≤ C := by
    intro x hx
    have h0 := hinv.bound 0 (by omega) x hx
    rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at h0
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rwa [le_div_iff₀ hpos] at h0
  rw [heatProfile_eq_average hh u τ,
    integral_average_inner hh (hinv.smooth.continuousOn) hb hψ]
  set lam := Real.exp (τ / 2) with hlam
  have hlam0 : 0 < lam := Real.exp_pos _
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  set f : Space → ℝ := fun w => inner ℝ (u w) (kconv h ψ (lam⁻¹ • w)) with hf
  have hcv := MeasureTheory.Measure.integral_comp_smul (volume : Measure Space) f lam
  rw [hfin] at hcv
  have he : ∀ x : Space, inner ℝ (dil τ u x) (kconv h ψ x) = lam * f (lam • x) := by
    intro x
    simp only [hf, dil, inner_smul_left, smul_smul, inv_mul_cancel₀ hlam0.ne', one_smul]
    rfl
  simp only [he]
  rw [integral_const_mul, hcv, abs_of_pos (inv_pos.mpr (pow_pos hlam0 3)), smul_eq_mul,
    ← mul_assoc]
  have hinv' : lam⁻¹ = Real.exp (-(τ / 2)) := by rw [hlam, Real.exp_neg]
  have hc : lam * (lam ^ 3)⁻¹ = Real.exp (-τ) := by
    rw [pow_succ', mul_inv, ← mul_assoc, mul_inv_cancel₀ hlam0.ne', one_mul, ← inv_pow,
      hinv', ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hc, hf, hinv']

end UnforcedLeray.Blueprint.HypBg
