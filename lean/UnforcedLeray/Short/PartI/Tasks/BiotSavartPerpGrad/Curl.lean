import UnforcedLeray.Short.PartI.Sub.S04
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.Polar.Fubini
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Part I, task `PartI:S04` (curl): `curl K q = q` (`BiotSavartCurl`)

Source of record: `the November 2 reference manuscript` (the curl identity cited in
`Short/PartI/Sub/S04.lean`, `BiotSavartCurl`).

Route. For fixed `y`, substitute `t = y - z` to write `K₁(∂₁q)(y) - K₀(∂₂q)(y)` as the integral of
`curlKer q y t = K₁(t) ∂₁q(y - t) - K₀(t) ∂₂q(y - t)`. Pass to polar coordinates about `0`
(`UnforcedLeray.PlanarBS.Polar.integral_eq_integral_Ioi_intervalIntegral`). On the ray of angle `θ`,
`r · curlKer q y (r e^{iθ}) = -(2π)⁻¹ ∂_r [q(y - r e^{iθ})]`, so the radial integral of
`∂_r g(·,θ)` over `(0,∞)` is `-g(0,θ) = -q y` (FTC, `g → 0` at `∞`), and the angular integral gives
`-(2π)⁻¹ · 2π · (-q y) = q y`. The swap of the `r`- and `θ`-integrals uses the integrability from the
polar Fubini lemma.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

namespace BiotSavartCurlAux

/-! ### Gaussian bounds -/

/-- `exp(-b |y|²)` is integrable on `ℂ` for `b > 0`. -/
theorem integrable_exp_neg_mul_sq_norm' {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : ℂ => Real.exp (-b * ‖y‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (b : ℂ)) (by simpa using hb) 0 0).re
  change Integrable (fun y : ℂ => (Complex.exp
    (-(b : ℂ) * ‖y‖ ^ 2 + 0 * inner ℝ (0 : ℂ) y)).re) at h
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re] using h

theorem integrable_exp_neg_sq_div_eight :
    Integrable (fun z : ℂ => Real.exp (-(‖z‖ ^ 2) / 8)) := by
  refine (integrable_exp_neg_mul_sq_norm' (b := 1 / 8) (by norm_num)).congr
    (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  congr 1
  ring

/-- `(1 + s)^N e^{-s²/8} ≤ e^{2N²}` for `s ≥ 0`. -/
theorem poly_mul_exp_le (N : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (1 + s) ^ N * Real.exp (-(s ^ 2) / 8) ≤ Real.exp (2 * (N : ℝ) ^ 2) := by
  have h1 : 1 + s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have h2 : (1 + s) ^ N ≤ Real.exp s ^ N := pow_le_pow_left₀ (by linarith) h1 N
  have h4 : (1 + s) ^ N * Real.exp (-(s ^ 2) / 8) ≤
      Real.exp ((N : ℝ) * s) * Real.exp (-(s ^ 2) / 8) := by
    rw [Real.exp_nat_mul]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  rw [← Real.exp_add] at h4
  refine h4.trans (Real.exp_le_exp.mpr ?_)
  nlinarith [sq_nonneg (s - 4 * (N : ℝ))]

/-- Domination by a Gaussian with half the exponent. -/
theorem gauss_dominated {C : ℝ} {N : ℕ} (z : ℂ) {x : ℝ}
    (hx : x ≤ C * (1 + ‖z‖) ^ N * Real.exp (-(‖z‖ ^ 2) / 4)) :
    x ≤ |C| * Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(‖z‖ ^ 2) / 8) := by
  have hE : Real.exp (-(‖z‖ ^ 2) / 4) =
      Real.exp (-(‖z‖ ^ 2) / 8) * Real.exp (-(‖z‖ ^ 2) / 8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hk := poly_mul_exp_le N (norm_nonneg z)
  have hA : 0 ≤ (1 + ‖z‖) ^ N := by positivity
  have hEp : 0 < Real.exp (-(‖z‖ ^ 2) / 8) := Real.exp_pos _
  have h4 : |C| * ((1 + ‖z‖) ^ N * Real.exp (-(‖z‖ ^ 2) / 8)) ≤
      |C| * Real.exp (2 * (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hk (abs_nonneg C)
  have hCA : C * (1 + ‖z‖) ^ N ≤ |C| * (1 + ‖z‖) ^ N :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hA
  have h5 : C * (1 + ‖z‖) ^ N * Real.exp (-(‖z‖ ^ 2) / 4) ≤
      |C| * ((1 + ‖z‖) ^ N * Real.exp (-(‖z‖ ^ 2) / 8)) * Real.exp (-(‖z‖ ^ 2) / 8) := by
    rw [hE]
    calc C * (1 + ‖z‖) ^ N * (Real.exp (-(‖z‖ ^ 2) / 8) * Real.exp (-(‖z‖ ^ 2) / 8))
        ≤ |C| * (1 + ‖z‖) ^ N * (Real.exp (-(‖z‖ ^ 2) / 8) * Real.exp (-(‖z‖ ^ 2) / 8)) :=
          mul_le_mul_of_nonneg_right hCA (by positivity)
      _ = |C| * ((1 + ‖z‖) ^ N * Real.exp (-(‖z‖ ^ 2) / 8)) * Real.exp (-(‖z‖ ^ 2) / 8) := by
          ring
  calc x ≤ C * (1 + ‖z‖) ^ N * Real.exp (-(‖z‖ ^ 2) / 4) := hx
    _ ≤ _ := h5
    _ ≤ _ := mul_le_mul_of_nonneg_right h4 hEp.le

/-! ### Integrability of kernel products -/

/-- `K · h` is integrable for continuous bounded integrable `h`. -/
theorem integrable_kernel_mul {i : Fin 2} {h : ℂ → ℂ} (hc : Continuous h) {K : ℝ}
    (hK : ∀ z, ‖h z‖ ≤ K) (hi : Integrable h) :
    Integrable (fun t => B0009.kernel i t * h t) := by
  have hn : Integrable ((ball (0 : ℂ) 1).indicator (B0009.kernel i)) volume :=
    (B0009.integrableOn_kernel_ball i).integrable_indicator measurableSet_ball
  have hkf_meas : Measurable ((ball (0 : ℂ) 1)ᶜ.indicator (B0009.kernel i)) :=
    (B0009.measurable_kernel i).indicator measurableSet_ball.compl
  have hkf_le : ∀ z, ‖(ball (0 : ℂ) 1)ᶜ.indicator (B0009.kernel i) z‖ ≤ (2 * Real.pi)⁻¹ := by
    intro z
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · rw [indicator_of_notMem (Set.notMem_compl_iff.2 hz), norm_zero]
      positivity
    · rw [indicator_of_mem (mem_compl hz)]
      exact B0009.norm_kernel_le_of_notMem_ball i hz
  have hsum : B0009.kernel i = (ball (0 : ℂ) 1).indicator (B0009.kernel i) +
      (ball (0 : ℂ) 1)ᶜ.indicator (B0009.kernel i) :=
    (indicator_self_add_compl _ _).symm
  have hpt : ∀ t, B0009.kernel i t * h t =
      (ball (0 : ℂ) 1).indicator (B0009.kernel i) t * h t +
        (ball (0 : ℂ) 1)ᶜ.indicator (B0009.kernel i) t * h t := by
    intro t
    have h' := congrFun hsum t
    rw [Pi.add_apply] at h'
    rw [h', add_mul]
  refine Integrable.congr
    ((hn.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hK)).add
      (hi.bdd_mul hkf_meas.aestronglyMeasurable (ae_of_all _ hkf_le)))
    (Filter.Eventually.of_forall fun t => ?_)
  exact (hpt t).symm

/-- The Biot-Savart integrand `z ↦ K(y - z) h(z)` is integrable. -/
theorem integrable_conv_kernel {i : Fin 2} {h : ℂ → ℂ} (y : ℂ) (hc : Continuous h) {K : ℝ}
    (hK : ∀ z, ‖h z‖ ≤ K) (hi : Integrable h) :
    Integrable (fun z => B0009.kernel i (y - z) * h z) := by
  have hc' : Continuous (fun t => h (y - t)) := hc.comp (continuous_const.sub continuous_id)
  have h1 : Integrable (fun t => B0009.kernel i t * h (y - t)) :=
    integrable_kernel_mul hc' (fun t => hK (y - t)) (hi.comp_sub_left y)
  have h2 := h1.comp_sub_left y
  simpa only [sub_sub_cancel] using h2

/-! ### Derivatives of `q` -/

/-- Linearity of `fderiv` in the direction: `Dq(w)v = v₁ ∂₁q(w) + v₂ ∂₂q(w)`. -/
theorem fderiv_apply_eq (q : ℂ → ℂ) (w v : ℂ) :
    fderiv ℝ q w v = (v.re : ℂ) * fderiv ℝ q w 1 + (v.im : ℂ) * fderiv ℝ q w Complex.I := by
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- A unit-direction derivative is dominated by the operator norm of `fderiv`. -/
theorem fderiv_apply_dom {q : ℂ → ℂ} {C : ℝ} {N : ℕ}
    (hd : ∀ z, ‖fderiv ℝ q z‖ ≤ C * (1 + ‖z‖) ^ N * Real.exp (-(‖z‖ ^ 2) / 4))
    {v : ℂ} (hv : ‖v‖ = 1) (z : ℂ) :
    ‖fderiv ℝ q z v‖ ≤ |C| * Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(‖z‖ ^ 2) / 8) := by
  refine gauss_dominated z ?_
  calc ‖fderiv ℝ q z v‖ ≤ ‖fderiv ℝ q z‖ * ‖v‖ := (fderiv ℝ q z).le_opNorm v
    _ = ‖fderiv ℝ q z‖ := by rw [hv, mul_one]
    _ ≤ _ := hd z

/-! ### The curl integrand and its polar form -/

/-- The integrand `t ↦ K₁(t) ∂₁q(y - t) - K₀(t) ∂₂q(y - t)` of the curl identity. -/
def curlKer (q : ℂ → ℂ) (y t : ℂ) : ℂ :=
  B0009.kernel 1 t * fderiv ℝ q (y - t) 1 - B0009.kernel 0 t * fderiv ℝ q (y - t) Complex.I

/-- The `r`-derivative of `r ↦ q(y - r e^{iθ})`. -/
def radDeriv (q : ℂ → ℂ) (y : ℂ) (r θ : ℝ) : ℂ :=
  fderiv ℝ q (y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    (-(Complex.exp ((θ : ℂ) * Complex.I)))

theorem perpComp_zero' (z : ℂ) : B0009.perpComp 0 z = -z.im := rfl

theorem perpComp_one' (z : ℂ) : B0009.perpComp 1 z = z.re := rfl

/-- Pointwise polar identity: `r · curlKer q y (r e^{iθ}) = -(2π)⁻¹ ∂_r g(r, θ)`. -/
theorem curlKer_polar (q : ℂ → ℂ) (y : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (r : ℂ) * curlKer q y (circleMap 0 r θ) = -(1 / (2 * (Real.pi : ℂ))) * radDeriv q y r θ := by
  have hv : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hnorm : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
    rw [norm_mul, hv, Complex.norm_real, Real.norm_of_nonneg hr.le, mul_one]
  have hre : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re =
      r * (Complex.exp ((θ : ℂ) * Complex.I)).re := Complex.re_ofReal_mul _ _
  have him : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im =
      r * (Complex.exp ((θ : ℂ) * Complex.I)).im := Complex.im_ofReal_mul _ _
  have hdec : radDeriv q y r θ = -(((Complex.exp ((θ : ℂ) * Complex.I)).re : ℂ) *
      fderiv ℝ q (y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) 1 +
      ((Complex.exp ((θ : ℂ) * Complex.I)).im : ℂ) *
      fderiv ℝ q (y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) Complex.I) := by
    unfold radDeriv
    rw [map_neg, fderiv_apply_eq q (y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I))]
  rw [circleMap_zero, hdec]
  unfold curlKer
  simp only [B0009.kernel, perpComp_zero', perpComp_one', hnorm, hre, him]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-! ### Radial calculus along the rays -/

/-- `r ↦ q(y - r e^{iθ})` has derivative `radDeriv q y r θ`. -/
theorem hasDerivAt_radial (q : ℂ → ℂ) (hqc : ContDiff ℝ ∞ q) (y : ℂ) (θ r : ℝ) :
    HasDerivAt (fun s : ℝ => q (y - (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
      (radDeriv q y r θ) r := by
  unfold radDeriv
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have hin : HasDerivAt (fun s : ℝ => y - (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      (-(Complex.exp ((θ : ℂ) * Complex.I))) r := by
    simpa using (h1.mul_const (Complex.exp ((θ : ℂ) * Complex.I))).const_sub y
  have hq : HasFDerivAt q (fderiv ℝ q (y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
      (y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :=
    ((hqc.differentiable (by simp)) _).hasFDerivAt
  exact hq.comp_hasDerivAt r hin

/-- Along each ray `q(y - r e^{iθ}) → 0` as `r → ∞`. -/
theorem tendsto_radial_zero (q : ℂ → ℂ) {K : ℝ} (y : ℂ) (θ : ℝ)
    (hK : ∀ z, ‖q z‖ ≤ K * Real.exp (-(‖z‖ ^ 2) / 8)) :
    Tendsto (fun r : ℝ => q (y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) atTop (𝓝 0) := by
  have hv : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hlow : ∀ r : ℝ, r + -‖y‖ ≤ ‖y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
    intro r
    have h1 : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = |r| := by
      rw [norm_mul, hv, Complex.norm_real, mul_one, Real.norm_eq_abs]
    have h2 := norm_sub_norm_le ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) y
    rw [h1, norm_sub_rev] at h2
    linarith [le_abs_self r]
  have hs : Tendsto (fun r : ℝ => ‖y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖)
      atTop atTop :=
    tendsto_atTop_mono hlow (tendsto_atTop_add_const_right _ (-‖y‖) tendsto_id)
  have hsq : Tendsto
      (fun r : ℝ => ‖y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hs
  have hneg : Tendsto
      (fun r : ℝ => -(‖y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2) / 8)
      atTop atBot :=
    Tendsto.atBot_div_const (by norm_num) (tendsto_neg_atTop_atBot.comp hsq)
  have hexp : Tendsto (fun r : ℝ =>
      K * Real.exp (-(‖y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2) / 8))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp hneg).const_mul K
    rw [mul_zero] at h
    exact h
  exact squeeze_zero_norm (fun r => hK _) hexp

/-- Radial integral: `∫_0^∞ ∂_r g(r, θ) dr = -g(0, θ) = -q y` when integrable. -/
theorem integral_radDeriv_eq (q : ℂ → ℂ) (hqc : ContDiff ℝ ∞ q) (y : ℂ) {K : ℝ}
    (hK : ∀ z, ‖q z‖ ≤ K * Real.exp (-(‖z‖ ^ 2) / 8)) (θ : ℝ)
    (hint : Integrable (fun r : ℝ => radDeriv q y r θ) (volume.restrict (Ioi (0 : ℝ)))) :
    ∫ r in Ioi (0 : ℝ), radDeriv q y r θ = -q y := by
  have hcont : ContinuousWithinAt
      (fun r : ℝ => q (y - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    exact hqc.continuous.comp
      (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const))
  have hfun := integral_Ioi_of_hasDerivAt_of_tendsto
    (f' := fun r : ℝ => radDeriv q y r θ) hcont
    (fun r _ => hasDerivAt_radial q hqc y θ r) hint (tendsto_radial_zero q y θ hK)
  exact hfun.trans (by simp)

end BiotSavartCurlAux

open BiotSavartCurlAux

/-- **Curl identity** `curl K q = q` (source lines 788-803, as cited in `S04.lean`). -/
theorem biotSavartCurl : BiotSavartCurl := by
  intro q hG y
  obtain ⟨hqc, hqb⟩ := hG
  obtain ⟨C0, N0, hC0⟩ := hqb 0
  obtain ⟨C1, N1, hC1⟩ := hqb 1
  -- Gaussian bounds for `q` and its derivative
  have hq_dom : ∀ z, ‖q z‖ ≤ |C0| * Real.exp (2 * (N0 : ℝ) ^ 2) * Real.exp (-(‖z‖ ^ 2) / 8) :=
    fun z => gauss_dominated z (by have := hC0 z; rwa [norm_iteratedFDeriv_zero] at this)
  have hd_dom : ∀ z, ‖fderiv ℝ q z‖ ≤ C1 * (1 + ‖z‖) ^ N1 * Real.exp (-(‖z‖ ^ 2) / 4) :=
    fun z => by have := hC1 z; rwa [norm_iteratedFDeriv_one] at this
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, ∀ z, ‖q z‖ ≤ K0 * Real.exp (-(‖z‖ ^ 2) / 8) :=
    ⟨_, hq_dom⟩
  obtain ⟨K1, hK1nn, hK1⟩ : ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ v : ℂ, ‖v‖ = 1 → ∀ z : ℂ,
      ‖fderiv ℝ q z v‖ ≤ K1 * Real.exp (-(‖z‖ ^ 2) / 8) :=
    ⟨|C1| * Real.exp (2 * (N1 : ℝ) ^ 2), by positivity,
      fun v hv z => fderiv_apply_dom hd_dom hv z⟩
  have hb1 : ∀ z, ‖fderiv ℝ q z 1‖ ≤ K1 := fun z =>
    (hK1 1 (by simp) z).trans (mul_le_of_le_one_right hK1nn
      (Real.exp_le_one_iff.mpr (by linarith [sq_nonneg ‖z‖])))
  have hbI : ∀ z, ‖fderiv ℝ q z Complex.I‖ ≤ K1 := fun z =>
    (hK1 Complex.I Complex.norm_I z).trans (mul_le_of_le_one_right hK1nn
      (Real.exp_le_one_iff.mpr (by linarith [sq_nonneg ‖z‖])))
  have hcd1 : Continuous (fun z => fderiv ℝ q z 1) :=
    (hqc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdI : Continuous (fun z => fderiv ℝ q z Complex.I) :=
    (hqc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi1 : Integrable (fun z => fderiv ℝ q z 1) :=
    Integrable.mono' (integrable_exp_neg_sq_div_eight.const_mul K1) hcd1.aestronglyMeasurable
      (ae_of_all _ fun z => hK1 1 (by simp) z)
  have hiI : Integrable (fun z => fderiv ℝ q z Complex.I) :=
    Integrable.mono' (integrable_exp_neg_sq_div_eight.const_mul K1) hcdI.aestronglyMeasurable
      (ae_of_all _ fun z => hK1 Complex.I Complex.norm_I z)
  -- kernel integrability
  have hA1 : Integrable (fun t => B0009.kernel 1 t * fderiv ℝ q (y - t) 1) :=
    integrable_kernel_mul (i := 1) (h := fun t => fderiv ℝ q (y - t) 1)
      (hcd1.comp (continuous_const.sub continuous_id)) (fun t => hb1 (y - t))
      (hi1.comp_sub_left y)
  have hA0 : Integrable (fun t => B0009.kernel 0 t * fderiv ℝ q (y - t) Complex.I) :=
    integrable_kernel_mul (i := 0) (h := fun t => fderiv ℝ q (y - t) Complex.I)
      (hcdI.comp (continuous_const.sub continuous_id)) (fun t => hbI (y - t))
      (hiI.comp_sub_left y)
  have hGint : Integrable (curlKer q y) := by
    unfold curlKer
    exact hA1.sub hA0
  have hConv1 : Integrable (fun z => B0009.kernel 1 (y - z) * fderiv ℝ q z 1) :=
    integrable_conv_kernel (i := 1) (h := fun z => fderiv ℝ q z 1) y hcd1 hb1 hi1
  have hConv0 : Integrable (fun z => B0009.kernel 0 (y - z) * fderiv ℝ q z Complex.I) :=
    integrable_conv_kernel (i := 0) (h := fun z => fderiv ℝ q z Complex.I) y hcdI hbI hiI
  -- step 1: convolution form to the `t`-integral of `curlKer`
  have hlhs : B0009.biotSavart (fun z => fderiv ℝ q z 1) 1 y -
      B0009.biotSavart (fun z => fderiv ℝ q z Complex.I) 0 y = ∫ t, curlKer q y t := by
    simp only [B0009.biotSavart_apply]
    rw [← integral_sub hConv1 hConv0]
    rw [← integral_sub_left_eq_self (curlKer q y) volume y]
    congr 1
    funext z
    simp only [curlKer, sub_sub_cancel]
  -- step 2: polar Fubini about `0`
  have hpolar := UnforcedLeray.PlanarBS.Polar.integral_eq_integral_Ioi_intervalIntegral hGint
  have hpt : ∀ r ∈ Ioi (0 : ℝ), r • ∫ θ in (0 : ℝ)..2 * Real.pi, curlKer q y (circleMap 0 r θ) =
      -(1 / (2 * (Real.pi : ℂ))) * ∫ θ in (0 : ℝ)..2 * Real.pi, radDeriv q y r θ := by
    intro r hr
    rw [Complex.real_smul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun θ _ => curlKer_polar q y hr θ)
  have hstep1 : ∫ r in Ioi (0 : ℝ), r • ∫ θ in (0 : ℝ)..2 * Real.pi, curlKer q y (circleMap 0 r θ)
      = ∫ r in Ioi (0 : ℝ),
        -(1 / (2 * (Real.pi : ℂ))) * ∫ θ in (0 : ℝ)..2 * Real.pi, radDeriv q y r θ :=
    setIntegral_congr_fun measurableSet_Ioi (fun r hr => hpt r hr)
  -- step 3: integrability of the radial derivative on the polar domain
  have hS : IntegrableOn (fun p : ℝ × ℝ => radDeriv q y p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) := by
    have hπC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h1 := UnforcedLeray.PlanarBS.Polar.integrableOn_polar hGint
    have h2 : IntegrableOn (fun p : ℝ × ℝ => -(1 / (2 * (Real.pi : ℂ))) * radDeriv q y p.1 p.2)
        (Ioi (0 : ℝ) ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) :=
      IntegrableOn.congr_fun h1
        (fun p hp => by
          simp only [Complex.real_smul]
          exact curlKer_polar q y (r := p.1) hp.1 p.2)
        (measurableSet_Ioi.prod measurableSet_Ioc)
    have h3 := Integrable.const_mul h2 (-(2 * (Real.pi : ℂ)))
    exact IntegrableOn.congr_fun h3
      (fun p _ => by
        field_simp)
      (measurableSet_Ioi.prod measurableSet_Ioc)
  have hPint : Integrable (fun p : ℝ × ℝ => radDeriv q y p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hS
  -- step 4: swap the radial and angular integrals
  have hswap : ∫ r in Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..2 * Real.pi, radDeriv q y r θ =
      ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ r in Ioi (0 : ℝ), radDeriv q y r θ := by
    simp only [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact integral_integral_swap (f := fun r θ => radDeriv q y r θ) hPint
  -- step 5: the radial integral is `-q y` for a.e. angle
  have hae : ∀ᵐ θ ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))),
      ∫ r in Ioi (0 : ℝ), radDeriv q y r θ = -q y := by
    filter_upwards [hPint.prod_left_ae] with θ hθ
    exact integral_radDeriv_eq q hqc y hK0 θ hθ
  -- step 6: assemble
  calc B0009.biotSavart (fun z => fderiv ℝ q z 1) 1 y -
        B0009.biotSavart (fun z => fderiv ℝ q z Complex.I) 0 y
      = ∫ t, curlKer q y t := hlhs
    _ = ∫ r in Ioi (0 : ℝ), r • ∫ θ in (0 : ℝ)..2 * Real.pi, curlKer q y (circleMap 0 r θ) :=
        hpolar
    _ = ∫ r in Ioi (0 : ℝ),
        -(1 / (2 * (Real.pi : ℂ))) * ∫ θ in (0 : ℝ)..2 * Real.pi, radDeriv q y r θ := hstep1
    _ = -(1 / (2 * (Real.pi : ℂ))) *
        ∫ r in Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..2 * Real.pi, radDeriv q y r θ :=
        integral_const_mul _ _
    _ = -(1 / (2 * (Real.pi : ℂ))) *
        ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ r in Ioi (0 : ℝ), radDeriv q y r θ := by
        rw [hswap]
    _ = -(1 / (2 * (Real.pi : ℂ))) *
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ∫ r in Ioi (0 : ℝ), radDeriv q y r θ := by
        rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    _ = -(1 / (2 * (Real.pi : ℂ))) * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), -q y := by
        congr 1
        exact integral_congr_ae hae
    _ = q y := by
        rw [setIntegral_const, Complex.real_smul, Real.volume_real_Ioc_of_le Real.two_pi_pos.le]
        have hπC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        push_cast
        field_simp
        ring

end UnforcedLeray.Short.PartI
