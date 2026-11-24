import UnforcedLeray.Short.PartI.Sub.S04
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# `BiotSavartDecay`: the Biot-Savart velocity tends to `0` at infinity

Source of record: `the November 2 reference manuscript`, lines 788-803.
For `q` in the Gaussian class and `i : Fin 2`, `B0009.biotSavart q i (y) → 0` as `y → ∞`.

Route. Split the kernel `K_i = kn + kf` with `kn = 1_{B₁} K_i` (integrable) and
`kf = 1_{B₁ᶜ} K_i` (bounded by `(2π)⁻¹` and by `(2π‖·‖)⁻¹`). Then
`K_i q (y) = ∫ kn(t) q(y - t) dt + ∫ kf(y - z) q(z) dz`.
* The first integral tends to `0` by dominated convergence, with the `y`-free bound
  `|kn(t)| sup|q|`, because `q(y - t) → 0` as `y → ∞` for each fixed `t`.
* The second tends to `0` by dominated convergence, with the `y`-free bound `(2π)⁻¹ |q(z)|`,
  because `kf(y - z) → 0` as `y → ∞` for each fixed `z`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-! ### Gaussian estimates -/

theorem bdDec_poly_gauss (C : ℝ) (N : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    C * (1 + a) ^ N * Real.exp (-(a ^ 2) / 4) ≤
      |C| * Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(a ^ 2) / 8) := by
  have h1 : (1 + a) ^ N ≤ Real.exp ((N : ℝ) * a) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp a]) N
  have hX : 0 ≤ (1 + a) ^ N * Real.exp (-(a ^ 2) / 4) := by positivity
  have h2 : (1 + a) ^ N * Real.exp (-(a ^ 2) / 4) ≤
      Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(a ^ 2) / 8) := by
    calc (1 + a) ^ N * Real.exp (-(a ^ 2) / 4)
        ≤ Real.exp ((N : ℝ) * a) * Real.exp (-(a ^ 2) / 4) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp ((N : ℝ) * a + -(a ^ 2) / 4) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (2 * (N : ℝ) ^ 2 + -(a ^ 2) / 8) :=
          Real.exp_le_exp.2 (by nlinarith [sq_nonneg (a - 4 * (N : ℝ))])
      _ = Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(a ^ 2) / 8) := Real.exp_add _ _
  calc C * (1 + a) ^ N * Real.exp (-(a ^ 2) / 4)
      = C * ((1 + a) ^ N * Real.exp (-(a ^ 2) / 4)) := by ring
    _ ≤ |C| * ((1 + a) ^ N * Real.exp (-(a ^ 2) / 4)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hX
    _ ≤ |C| * (Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(a ^ 2) / 8)) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    _ = |C| * Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(a ^ 2) / 8) := by ring

/-- The Gaussian `exp(-‖t‖²/8)` is integrable on `ℂ`. -/
theorem bdDec_gauss_int : Integrable (fun t : ℂ => Real.exp (-(‖t‖ ^ 2) / 8)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ)
    (b := ((1 / 8 : ℝ) : ℂ)) (by norm_num) 0 0).re
  change Integrable (fun x : ℂ => (Complex.exp
    (-((1 / 8 : ℝ) : ℂ) * ‖x‖ ^ 2 + 0 * inner ℝ (0 : ℂ) x)).re) at h
  have h2 : Integrable (fun x : ℂ => Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) := by
    simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re] using h
  refine h2.congr (ae_of_all _ fun x => ?_)
  show Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) = Real.exp (-(‖x‖ ^ 2) / 8)
  congr 1
  ring

/-- Gaussian bound on `q` from the `k = 0` bound of `PlanarGaussianClass`. -/
theorem bdDec_gauss_bound {q : ℂ → ℂ} {C : ℝ} {N : ℕ}
    (hC : ∀ y, ‖iteratedFDeriv ℝ 0 q y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4))
    (w : ℂ) : ‖q w‖ ≤ |C| * Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(‖w‖ ^ 2) / 8) := by
  have h := hC w
  rw [norm_iteratedFDeriv_zero] at h
  exact h.trans (bdDec_poly_gauss C N ‖w‖ (norm_nonneg w))

/-- `q` is bounded. -/
theorem bdDec_bounded {q : ℂ → ℂ} {C : ℝ} {N : ℕ}
    (hC : ∀ y, ‖iteratedFDeriv ℝ 0 q y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4))
    (w : ℂ) : ‖q w‖ ≤ |C| * Real.exp (2 * (N : ℝ) ^ 2) := by
  refine (bdDec_gauss_bound hC w).trans (mul_le_of_le_one_right (by positivity) ?_)
  exact Real.exp_le_one_iff.2 (by have := sq_nonneg ‖w‖; linarith)

/-- The Gaussian tends to `0` along `cocompact ℂ`. -/
theorem bdDec_gauss_tendsto :
    Tendsto (fun w : ℂ => Real.exp (-(‖w‖ ^ 2) / 8)) (cocompact ℂ) (𝓝 0) := by
  have hsq : Tendsto (fun w : ℂ => ‖w‖ ^ 2) (cocompact ℂ) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop
  have h8 : Tendsto (fun w : ℂ => ‖w‖ ^ 2 / 8) (cocompact ℂ) atTop :=
    hsq.atTop_div_const (by norm_num)
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp h8
  exact h.congr (fun w => by simp [neg_div])

/-- `q → 0` along `cocompact ℂ`. -/
theorem bdDec_tendsto_zero {q : ℂ → ℂ} {C : ℝ} {N : ℕ}
    (hC : ∀ y, ‖iteratedFDeriv ℝ 0 q y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) :
    Tendsto q (cocompact ℂ) (𝓝 0) := by
  have h := bdDec_gauss_tendsto.const_mul (|C| * Real.exp (2 * (N : ℝ) ^ 2))
  rw [mul_zero] at h
  exact squeeze_zero_norm (fun w => bdDec_gauss_bound hC w) h

/-- `q` is integrable. -/
theorem bdDec_integrable {q : ℂ → ℂ} {C : ℝ} {N : ℕ} (hcont : Continuous q)
    (hC : ∀ y, ‖iteratedFDeriv ℝ 0 q y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) :
    Integrable q :=
  Integrable.mono' (bdDec_gauss_int.const_mul (|C| * Real.exp (2 * (N : ℝ) ^ 2)))
    hcont.aestronglyMeasurable (ae_of_all _ fun w => bdDec_gauss_bound hC w)

/-! ### The near and far parts of the kernel -/

/-- The near part `1_{B₁} K_i` of the Biot-Savart kernel. -/
def bdKn (i : Fin 2) : ℂ → ℂ := (Metric.ball (0 : ℂ) 1).indicator (B0009.kernel i)

/-- The far part `1_{B₁ᶜ} K_i` of the Biot-Savart kernel. -/
def bdKf (i : Fin 2) : ℂ → ℂ := (Metric.ball (0 : ℂ) 1)ᶜ.indicator (B0009.kernel i)

theorem bdKsplit (i : Fin 2) : B0009.kernel i = bdKn i + bdKf i := by
  unfold bdKn bdKf
  exact (indicator_self_add_compl _ _).symm

theorem bdKn_meas (i : Fin 2) : Measurable (bdKn i) := by
  unfold bdKn
  exact (B0009.measurable_kernel i).indicator measurableSet_ball

theorem bdKf_meas (i : Fin 2) : Measurable (bdKf i) := by
  unfold bdKf
  exact (B0009.measurable_kernel i).indicator measurableSet_ball.compl

theorem bdKn_int (i : Fin 2) : Integrable (bdKn i) := by
  unfold bdKn
  exact (B0009.integrableOn_kernel_ball i).integrable_indicator measurableSet_ball

theorem bdKf_le1 (i : Fin 2) (w : ℂ) : ‖bdKf i w‖ ≤ (2 * Real.pi)⁻¹ := by
  unfold bdKf
  by_cases hz : w ∈ Metric.ball (0 : ℂ) 1
  · rw [indicator_of_notMem (Set.notMem_compl_iff.2 hz), norm_zero]
    positivity
  · rw [indicator_of_mem (mem_compl hz)]
    exact B0009.norm_kernel_le_of_notMem_ball i hz

theorem bdKf_le2 (i : Fin 2) (w : ℂ) : ‖bdKf i w‖ ≤ (2 * Real.pi * ‖w‖)⁻¹ := by
  unfold bdKf
  by_cases hz : w ∈ Metric.ball (0 : ℂ) 1
  · rw [indicator_of_notMem (Set.notMem_compl_iff.2 hz), norm_zero]
    positivity
  · rw [indicator_of_mem (mem_compl hz)]
    exact B0009.norm_kernel_le i w

/-! ### Cocompact filter helpers -/

theorem bdDec_cocompact_cg : (cocompact ℂ).IsCountablyGenerated := by
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]
  infer_instance

theorem bdDec_cc_sub (t : ℂ) : Tendsto (fun y : ℂ => y - t) (cocompact ℂ) (cocompact ℂ) := by
  have h := (Homeomorph.addRight (-t)).isClosedEmbedding.tendsto_cocompact
  refine h.congr (fun y => ?_)
  simp [sub_eq_add_neg]

theorem bdDec_norm_sub (t : ℂ) : Tendsto (fun y : ℂ => ‖y - t‖) (cocompact ℂ) atTop :=
  tendsto_norm_cocompact_atTop.comp (bdDec_cc_sub t)

theorem bdDec_inv_tendsto (z : ℂ) :
    Tendsto (fun y : ℂ => (2 * Real.pi * ‖y - z‖)⁻¹) (cocompact ℂ) (𝓝 0) := by
  have h1 : Tendsto (fun y : ℂ => 2 * Real.pi * ‖y - z‖) (cocompact ℂ) atTop :=
    Tendsto.const_mul_atTop (by positivity) (bdDec_norm_sub z)
  exact tendsto_inv_atTop_zero.comp h1

/-! ### The two dominated-convergence pieces -/

theorem bdDec_near_integrable {q kn : ℂ → ℂ} (hqc : Continuous q) {Cq : ℝ}
    (hqb : ∀ w, ‖q w‖ ≤ Cq) (hkn : Measurable kn) (hkni : Integrable kn) (y : ℂ) :
    Integrable (fun t : ℂ => kn t * q (y - t)) := by
  have hsub : Continuous fun t : ℂ => y - t := continuous_const.sub continuous_id
  have hc : Continuous fun t : ℂ => q (y - t) := hqc.comp hsub
  refine Integrable.mono' (hkni.norm.mul_const Cq) (hkn.mul hc.measurable).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  show ‖kn t * q (y - t)‖ ≤ ‖kn t‖ * Cq
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hqb _) (norm_nonneg _)

theorem bdDec_far_integrable {q kf : ℂ → ℂ} (hqi : Integrable q) (hqc : Continuous q)
    (hkfm : Measurable kf) (hkf1 : ∀ w, ‖kf w‖ ≤ (2 * Real.pi)⁻¹) (y : ℂ) :
    Integrable (fun z : ℂ => kf (y - z) * q z) := by
  have hsub : Measurable fun z : ℂ => y - z := (continuous_const.sub continuous_id).measurable
  refine Integrable.mono' (hqi.norm.const_mul ((2 * Real.pi)⁻¹))
    ((hkfm.comp hsub).mul hqc.measurable).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  show ‖kf (y - z) * q z‖ ≤ (2 * Real.pi)⁻¹ * ‖q z‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hkf1 _) (norm_nonneg _)

/-- The near part tends to `0`: dominated convergence in `t` with bound `|kn t| · sup|q|`. -/
theorem bdDec_near {q kn : ℂ → ℂ} (hqc : Continuous q)
    (hq0 : Tendsto q (cocompact ℂ) (𝓝 0)) {Cq : ℝ} (hqb : ∀ w, ‖q w‖ ≤ Cq)
    (hkn : Measurable kn) (hkni : Integrable kn) :
    Tendsto (fun y : ℂ => ∫ t, kn t * q (y - t)) (cocompact ℂ) (𝓝 0) := by
  have := bdDec_cocompact_cg
  have hmeas : ∀ y : ℂ, AEStronglyMeasurable (fun t : ℂ => kn t * q (y - t)) volume := by
    intro y
    have hsub : Continuous fun t : ℂ => y - t := continuous_const.sub continuous_id
    have hc : Continuous fun t : ℂ => q (y - t) := hqc.comp hsub
    exact (hkn.mul hc.measurable).aestronglyMeasurable
  have hb : Integrable (fun t : ℂ => ‖kn t‖ * Cq) := hkni.norm.mul_const Cq
  have hbd : ∀ y : ℂ, ∀ᵐ t ∂(volume : Measure ℂ), ‖kn t * q (y - t)‖ ≤ ‖kn t‖ * Cq := by
    intro y
    refine ae_of_all _ fun t => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hqb _) (norm_nonneg _)
  have hlim : ∀ᵐ t ∂(volume : Measure ℂ),
      Tendsto (fun y : ℂ => kn t * q (y - t)) (cocompact ℂ) (𝓝 ((fun _ : ℂ => (0 : ℂ)) t)) := by
    refine ae_of_all _ fun t => ?_
    have h := (hq0.comp (bdDec_cc_sub t)).const_mul (kn t)
    simpa using h
  have key := tendsto_integral_filter_of_dominated_convergence (l := cocompact ℂ)
    (fun t : ℂ => ‖kn t‖ * Cq)
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbd) hb hlim
  simpa using key

/-- The far part tends to `0`: dominated convergence in `z` with `y`-free bound `(2π)⁻¹ |q z|`. -/
theorem bdDec_far {q kf : ℂ → ℂ} (hqi : Integrable q) (hqc : Continuous q)
    (hkfm : Measurable kf) (hkf1 : ∀ w, ‖kf w‖ ≤ (2 * Real.pi)⁻¹)
    (hkf2 : ∀ w, ‖kf w‖ ≤ (2 * Real.pi * ‖w‖)⁻¹) :
    Tendsto (fun y : ℂ => ∫ z, kf (y - z) * q z) (cocompact ℂ) (𝓝 0) := by
  have := bdDec_cocompact_cg
  have hmeas : ∀ y : ℂ, AEStronglyMeasurable (fun z : ℂ => kf (y - z) * q z) volume := by
    intro y
    have hsub : Measurable fun z : ℂ => y - z := (continuous_const.sub continuous_id).measurable
    exact ((hkfm.comp hsub).mul hqc.measurable).aestronglyMeasurable
  have hb : Integrable (fun z : ℂ => (2 * Real.pi)⁻¹ * ‖q z‖) :=
    hqi.norm.const_mul ((2 * Real.pi)⁻¹)
  have hbd : ∀ y : ℂ, ∀ᵐ z ∂(volume : Measure ℂ),
      ‖kf (y - z) * q z‖ ≤ (2 * Real.pi)⁻¹ * ‖q z‖ := by
    intro y
    refine ae_of_all _ fun z => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hkf1 _) (norm_nonneg _)
  have hlim : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun y : ℂ => kf (y - z) * q z) (cocompact ℂ) (𝓝 ((fun _ : ℂ => (0 : ℂ)) z)) := by
    refine ae_of_all _ fun z => ?_
    have hpt : Tendsto (fun y : ℂ => kf (y - z)) (cocompact ℂ) (𝓝 0) :=
      squeeze_zero_norm (fun y => hkf2 (y - z)) (bdDec_inv_tendsto z)
    have h := hpt.mul_const (q z)
    simpa using h
  have key := tendsto_integral_filter_of_dominated_convergence (l := cocompact ℂ)
    (fun z : ℂ => (2 * Real.pi)⁻¹ * ‖q z‖)
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbd) hb hlim
  simpa using key

/-! ### Assembly -/

/-- **Decay of the Biot-Savart velocity** (source lines 788-803): `K_i q → 0` at infinity. -/
theorem biotSavartDecay : BiotSavartDecay := by
  unfold BiotSavartDecay
  intro q hq i
  unfold PlanarGaussianClass at hq
  obtain ⟨hsm, hgb⟩ := hq
  obtain ⟨C, N, hC⟩ := hgb 0
  have hcont : Continuous q := hsm.continuous
  have hq0 : Tendsto q (cocompact ℂ) (𝓝 0) := bdDec_tendsto_zero hC
  have hqi : Integrable q := bdDec_integrable hcont hC
  have hdec : B0009.biotSavart q i = fun y : ℂ =>
      (∫ t, bdKn i t * q (y - t)) + ∫ z, bdKf i (y - z) * q z := by
    funext y
    rw [B0009.biotSavart_apply]
    have hA : Integrable (fun t : ℂ => bdKn i t * q (y - t)) :=
      bdDec_near_integrable hcont (bdDec_bounded hC) (bdKn_meas i) (bdKn_int i) y
    have hA' : Integrable (fun z : ℂ => bdKn i (y - z) * q z) := by
      simpa [sub_sub_cancel] using hA.comp_sub_left y
    have hB : Integrable (fun z : ℂ => bdKf i (y - z) * q z) :=
      bdDec_far_integrable hqi hcont (bdKf_meas i) (bdKf_le1 i) y
    have hpt : ∀ z : ℂ, B0009.kernel i (y - z) * q z =
        bdKn i (y - z) * q z + bdKf i (y - z) * q z := by
      intro z
      rw [bdKsplit i, Pi.add_apply, add_mul]
    simp_rw [hpt]
    rw [integral_add hA' hB]
    congr 1
    have h := integral_sub_left_eq_self (fun t : ℂ => bdKn i t * q (y - t)) volume y
    simpa [sub_sub_cancel] using h
  rw [hdec]
  have hsum := (bdDec_near hcont hq0 (bdDec_bounded hC) (bdKn_meas i) (bdKn_int i)).add
    (bdDec_far hqi hcont (bdKf_meas i) (bdKf_le1 i) (bdKf_le2 i))
  simpa only [add_zero] using hsum

end UnforcedLeray.Short.PartI
