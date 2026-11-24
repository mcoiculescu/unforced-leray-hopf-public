import UnforcedLeray.Short.PartI.Sub.S04
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.Polar.Fubini
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Part I, task `PartI:S04/2`: `K₀(∂₁q) + K₁(∂₂q) = 0` (divergence free Biot-Savart)

Source of record: `the November 2 reference manuscript`. The divergence-free
identity is the angular half of the Green identity for the kernel `K = ∇^⊥ N` (the Lean statement
`BiotSavartDivFree` in `Sub/S04.lean`).

Proof. Fix `y`. Substituting `z = y - t` (`integral_sub_left_eq_self`) turns the sum into
`∫ K(t) · (∂q)(y - t) dt`, with `K₀ = -t₂/(2π|t|²)` and `K₁ = t₁/(2π|t|²)`. Pointwise,
`K₀(t) ∂₁q(w) + K₁(t) ∂₂q(w) = (2π|t|²)⁻¹ ∂q(w)(i t)` for `w = y - t`. Polar coordinates
(`UnforcedLeray.PlanarBS.Polar.integral_eq_integral_Ioi_intervalIntegral`) reduce the claim to
`∫₀^{2π} ∂q(y - r e^{iθ})(i r e^{iθ}) dθ = 0` for each `r`. This is the fundamental theorem of
calculus for `θ ↦ q(y - r e^{iθ})`, whose derivative is `-∂q(y - t)(i t)`, and `2π`-periodicity.

Integrability: `|∂q(w)| ≤ B e^{-|w|²/8}` (from the Gaussian class with `k = 1`, using
`(1+s)^N ≤ e^{2N²} e^{s²/8}`), and `|K(t)| ≤ (2π|t|)⁻¹` with the near/far split at `|t| = 1`
(`B0009.integrableOn_kernel_ball`, `B0009.norm_kernel_le_of_notMem_ball`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-! ### Gaussian integrability on `ℂ` -/

theorem dvDiv_integrable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : ℂ => Real.exp (-b * ‖y‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (b : ℂ)) (by simpa using hb) 0 0).re
  change Integrable (fun y : ℂ => (Complex.exp
    (-(b : ℂ) * ‖y‖ ^ 2 + 0 * inner ℝ (0 : ℂ) y)).re) at h
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re] using h

theorem dvDiv_integrable_gauss_eighth :
    Integrable (fun y : ℂ => Real.exp (-(‖y‖ ^ 2) / 8)) := by
  refine (dvDiv_integrable_exp_neg_mul_sq (b := 1 / 8) (by norm_num)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  congr 1
  ring

/-- `(1+s)^N ≤ e^{2N²} e^{s²/8}` for `s ≥ 0` (from `1 + s ≤ e^s` and `N s ≤ 2N² + s²/8`). -/
theorem dvDiv_poly_le_exp (N : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (1 + s) ^ N ≤ Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (s ^ 2 / 8) := by
  have h1 : (1 + s) ^ N ≤ (Real.exp s) ^ N :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp s]) N
  have h2 : (N : ℝ) * s ≤ 2 * (N : ℝ) ^ 2 + s ^ 2 / 8 := by
    nlinarith [sq_nonneg (s - 4 * (N : ℝ))]
  calc (1 + s) ^ N ≤ (Real.exp s) ^ N := h1
    _ = Real.exp ((N : ℝ) * s) := (Real.exp_nat_mul s N).symm
    _ ≤ Real.exp (2 * (N : ℝ) ^ 2 + s ^ 2 / 8) := Real.exp_le_exp.mpr h2
    _ = Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (s ^ 2 / 8) := Real.exp_add _ _

/-- Gaussian decay of the derivative: `‖∂q(w)‖ ≤ B e^{-|w|²/8}` with `B ≥ 0`. -/
theorem dvDiv_fderiv_gauss {q : ℂ → ℂ} (hq : PlanarGaussianClass q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, ‖fderiv ℝ q w‖ ≤ B * Real.exp (-(‖w‖ ^ 2) / 8) := by
  obtain ⟨_, hg⟩ := hq
  obtain ⟨C, N, hC⟩ := hg 1
  refine ⟨|C| * Real.exp (2 * (N : ℝ) ^ 2), by positivity, fun w => ?_⟩
  have hs : 0 ≤ ‖w‖ := norm_nonneg w
  have hE : 0 ≤ Real.exp (-(‖w‖ ^ 2) / 4) := (Real.exp_pos _).le
  have hX0 : 0 ≤ (1 + ‖w‖) ^ N * Real.exp (-(‖w‖ ^ 2) / 4) := by positivity
  have hX : (1 + ‖w‖) ^ N * Real.exp (-(‖w‖ ^ 2) / 4) ≤
      Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(‖w‖ ^ 2) / 8) := by
    calc (1 + ‖w‖) ^ N * Real.exp (-(‖w‖ ^ 2) / 4)
        ≤ (Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (‖w‖ ^ 2 / 8)) * Real.exp (-(‖w‖ ^ 2) / 4) :=
          mul_le_mul_of_nonneg_right (dvDiv_poly_le_exp N hs) hE
      _ = Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(‖w‖ ^ 2) / 8) := by
          rw [mul_assoc, ← Real.exp_add, show ‖w‖ ^ 2 / 8 + -(‖w‖ ^ 2) / 4 = -(‖w‖ ^ 2) / 8 by ring]
  have hfd : ‖fderiv ℝ q w‖ ≤ C * ((1 + ‖w‖) ^ N * Real.exp (-(‖w‖ ^ 2) / 4)) := by
    have h := hC w
    rw [norm_iteratedFDeriv_one, mul_assoc] at h
    exact h
  calc ‖fderiv ℝ q w‖ ≤ C * ((1 + ‖w‖) ^ N * Real.exp (-(‖w‖ ^ 2) / 4)) := hfd
    _ ≤ |C| * ((1 + ‖w‖) ^ N * Real.exp (-(‖w‖ ^ 2) / 4)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hX0
    _ ≤ |C| * (Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(‖w‖ ^ 2) / 8)) :=
        mul_le_mul_of_nonneg_left hX (abs_nonneg C)
    _ = |C| * Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(‖w‖ ^ 2) / 8) := by ring

theorem dvDiv_cont_apply {q : ℂ → ℂ} (hq : PlanarGaussianClass q) (v : ℂ) :
    Continuous (fun w => fderiv ℝ q w v) := by
  obtain ⟨hsm, _⟩ := hq
  exact (hsm.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The directional derivative `w ↦ ∂_v q(w)` is integrable and bounded. -/
theorem dvDiv_fderiv_integrable {q : ℂ → ℂ} (hq : PlanarGaussianClass q) (v : ℂ) :
    Integrable (fun w => fderiv ℝ q w v) ∧ ∃ c : ℝ, ∀ w, ‖fderiv ℝ q w v‖ ≤ c := by
  obtain ⟨B, hB0, hB⟩ := dvDiv_fderiv_gauss hq
  have hbound : ∀ w : ℂ, ‖fderiv ℝ q w v‖ ≤ (B * ‖v‖) * Real.exp (-(‖w‖ ^ 2) / 8) := by
    intro w
    calc ‖fderiv ℝ q w v‖ ≤ ‖fderiv ℝ q w‖ * ‖v‖ := (fderiv ℝ q w).le_opNorm v
      _ ≤ (B * Real.exp (-(‖w‖ ^ 2) / 8)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (hB w) (norm_nonneg v)
      _ = (B * ‖v‖) * Real.exp (-(‖w‖ ^ 2) / 8) := by ring
  refine ⟨?_, B * ‖v‖, fun w => ?_⟩
  · exact Integrable.mono' (dvDiv_integrable_gauss_eighth.const_mul (B * ‖v‖))
      (dvDiv_cont_apply hq v).aestronglyMeasurable (ae_of_all _ hbound)
  · calc ‖fderiv ℝ q w v‖ ≤ (B * ‖v‖) * Real.exp (-(‖w‖ ^ 2) / 8) := hbound w
      _ ≤ (B * ‖v‖) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB0 (norm_nonneg v))
          rw [Real.exp_le_one_iff]
          have := sq_nonneg ‖w‖
          linarith
      _ = B * ‖v‖ := mul_one _

/-- Translated version: `t ↦ ∂_v q(y - t)` is integrable, measurable and bounded. -/
theorem dvDiv_shift_integrable {q : ℂ → ℂ} (hq : PlanarGaussianClass q) (y v : ℂ) :
    Integrable (fun t => fderiv ℝ q (y - t) v) ∧
      AEStronglyMeasurable (fun t => fderiv ℝ q (y - t) v) volume ∧
      ∃ c : ℝ, ∀ t, ‖fderiv ℝ q (y - t) v‖ ≤ c := by
  obtain ⟨hI, c, hc⟩ := dvDiv_fderiv_integrable hq v
  have hcs : Continuous (fun t : ℂ => y - t) := continuous_const.sub continuous_id
  exact ⟨hI.comp_sub_left y, ((dvDiv_cont_apply hq v).comp hcs).aestronglyMeasurable,
    c, fun t => hc (y - t)⟩

/-! ### Integrability of `kernel · g` -/

/-- `K_i · g` is integrable for `g` integrable and bounded (near/far split at `|t| = 1`). -/
theorem dvDiv_kernel_mul_integrable {g : ℂ → ℂ} (hg : Integrable g)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∃ c : ℝ, ∀ t, ‖g t‖ ≤ c) (i : Fin 2) :
    Integrable (fun t => B0009.kernel i t * g t) := by
  obtain ⟨c, hc⟩ := hgb
  set kn : ℂ → ℂ := (ball (0 : ℂ) 1).indicator (B0009.kernel i) with hkn
  set kf : ℂ → ℂ := (ball (0 : ℂ) 1)ᶜ.indicator (B0009.kernel i) with hkf
  have hn : Integrable kn volume :=
    (B0009.integrableOn_kernel_ball i).integrable_indicator measurableSet_ball
  have hkf_meas : Measurable kf :=
    (B0009.measurable_kernel i).indicator measurableSet_ball.compl
  have hkf_le : ∀ z, ‖kf z‖ ≤ (2 * Real.pi)⁻¹ := by
    intro z
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · rw [hkf, indicator_of_notMem (Set.notMem_compl_iff.2 hz), norm_zero]
      positivity
    · rw [hkf, indicator_of_mem (mem_compl hz)]
      exact B0009.norm_kernel_le_of_notMem_ball i hz
  have hsum : B0009.kernel i = kn + kf := (indicator_self_add_compl _ _).symm
  have key : (fun t => B0009.kernel i t * g t) = fun t => kn t * g t + kf t * g t := by
    funext t
    rw [hsum]
    simp only [Pi.add_apply, add_mul]
  rw [key]
  exact (hn.mul_bdd hgm (ae_of_all _ hc)).add
    (hg.bdd_mul hkf_meas.aestronglyMeasurable (ae_of_all _ hkf_le))

/-! ### The circle integral of the angular derivative vanishes -/

/-- `∫₀^{2π} ∂q(y - r e^{iθ})(i r e^{iθ}) dθ = 0`: the fundamental theorem of calculus for
`θ ↦ q(y - r e^{iθ})` (derivative `-∂q(y - t)(i t)`) and `2π`-periodicity. -/
theorem dvDiv_circle_integral_zero {q : ℂ → ℂ} (hq : PlanarGaussianClass q) (y : ℂ) (r : ℝ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      fderiv ℝ q (y - circleMap 0 r θ) (Complex.I * circleMap 0 r θ) = 0 := by
  obtain ⟨hsm, _⟩ := hq
  have hqd : Differentiable ℝ q := hsm.differentiable (by simp)
  have hqc : Continuous (fun w => fderiv ℝ q w) := hsm.continuous_fderiv (by simp)
  have hcirc : Continuous (fun θ : ℝ => circleMap 0 r θ) :=
    continuous_iff_continuousAt.2 fun θ => (hasDerivAt_circleMap 0 r θ).continuousAt
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (fun θ => q (y - circleMap 0 r θ))
        (-(fderiv ℝ q (y - circleMap 0 r θ) (Complex.I * circleMap 0 r θ))) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ => y - circleMap 0 r θ) (-(circleMap 0 r θ * Complex.I)) θ :=
      (hasDerivAt_circleMap 0 r θ).const_sub y
    have h2 := (hqd (y - circleMap 0 r θ)).hasFDerivAt.comp_hasDerivAt θ h1
    refine h2.congr_deriv ?_
    rw [map_neg, mul_comm]
  have hsub : Continuous (fun θ : ℝ => y - circleMap 0 r θ) := continuous_const.sub hcirc
  have hmul : Continuous (fun θ : ℝ => Complex.I * circleMap 0 r θ) := continuous_const.mul hcirc
  have hcont : Continuous (fun θ : ℝ =>
      fderiv ℝ q (y - circleMap 0 r θ) (Complex.I * circleMap 0 r θ)) :=
    (hqc.comp hsub).clm_apply hmul
  have key : ∫ θ in (0 : ℝ)..2 * Real.pi,
      -(fderiv ℝ q (y - circleMap 0 r θ) (Complex.I * circleMap 0 r θ)) =
      q (y - circleMap 0 r (2 * Real.pi)) - q (y - circleMap 0 r 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.neg.intervalIntegrable _ _)
  have hper : circleMap 0 r (2 * Real.pi) = circleMap 0 r 0 := by
    have h := periodic_circleMap 0 r 0
    simpa using h
  rw [hper, sub_self, intervalIntegral.integral_neg] at key
  exact neg_eq_zero.mp key

/-! ### The pointwise kernel identity -/

/-- `K₀(t) L(1) + K₁(t) L(i) = (2π|t|²)⁻¹ L(i t)` for every real-linear `L`. -/
theorem dvDiv_kernel_apply (L : ℂ →L[ℝ] ℂ) (t : ℂ) :
    B0009.kernel 0 t * L 1 + B0009.kernel 1 t * L Complex.I =
      (((2 * Real.pi * ‖t‖ ^ 2)⁻¹ : ℝ) : ℂ) * L (Complex.I * t) := by
  have hv : Complex.I * t = (-t.im : ℝ) • (1 : ℂ) + t.re • Complex.I := by
    apply Complex.ext <;> simp
  rw [hv, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  simp only [B0009.kernel, B0009.perpComp]
  push_cast
  ring

/-! ### Main theorem -/

theorem biotSavartDivFree : BiotSavartDivFree := by
  unfold BiotSavartDivFree
  intro q hq y
  have hT0 : Integrable (fun t => B0009.kernel 0 t * fderiv ℝ q (y - t) 1) := by
    obtain ⟨hI, hm, hb⟩ := dvDiv_shift_integrable hq y 1
    exact dvDiv_kernel_mul_integrable hI hm hb 0
  have hT1 : Integrable (fun t => B0009.kernel 1 t * fderiv ℝ q (y - t) Complex.I) := by
    obtain ⟨hI, hm, hb⟩ := dvDiv_shift_integrable hq y Complex.I
    exact dvDiv_kernel_mul_integrable hI hm hb 1
  have e0 : ∫ z, B0009.kernel 0 (y - z) * fderiv ℝ q z 1 =
      ∫ t, B0009.kernel 0 t * fderiv ℝ q (y - t) 1 := by
    have h := integral_sub_left_eq_self
      (fun z : ℂ => B0009.kernel 0 (y - z) * fderiv ℝ q z 1) volume y
    simp only [sub_sub_cancel] at h
    exact h.symm
  have e1 : ∫ z, B0009.kernel 1 (y - z) * fderiv ℝ q z Complex.I =
      ∫ t, B0009.kernel 1 t * fderiv ℝ q (y - t) Complex.I := by
    have h := integral_sub_left_eq_self
      (fun z : ℂ => B0009.kernel 1 (y - z) * fderiv ℝ q z Complex.I) volume y
    simp only [sub_sub_cancel] at h
    exact h.symm
  rw [B0009.biotSavart_apply, B0009.biotSavart_apply, e0, e1, ← integral_add hT0 hT1]
  have hΨ : Integrable (fun t => B0009.kernel 0 t * fderiv ℝ q (y - t) 1 +
      B0009.kernel 1 t * fderiv ℝ q (y - t) Complex.I) := hT0.add hT1
  rw [UnforcedLeray.PlanarBS.Polar.integral_eq_integral_Ioi_intervalIntegral hΨ]
  have hinner : ∀ r : ℝ, ∫ θ in (0 : ℝ)..2 * Real.pi,
      (B0009.kernel 0 (circleMap 0 r θ) * fderiv ℝ q (y - circleMap 0 r θ) 1 +
        B0009.kernel 1 (circleMap 0 r θ) * fderiv ℝ q (y - circleMap 0 r θ) Complex.I) = 0 := by
    intro r
    have hpt : ∀ θ : ℝ,
        (B0009.kernel 0 (circleMap 0 r θ) * fderiv ℝ q (y - circleMap 0 r θ) 1 +
          B0009.kernel 1 (circleMap 0 r θ) * fderiv ℝ q (y - circleMap 0 r θ) Complex.I) =
        (((2 * Real.pi * |r| ^ 2)⁻¹ : ℝ) : ℂ) *
          fderiv ℝ q (y - circleMap 0 r θ) (Complex.I * circleMap 0 r θ) := by
      intro θ
      rw [dvDiv_kernel_apply (fderiv ℝ q (y - circleMap 0 r θ)) (circleMap 0 r θ),
        norm_circleMap_zero]
    simp only [hpt]
    rw [intervalIntegral.integral_const_mul, dvDiv_circle_integral_zero hq y r, mul_zero]
  simp only [hinner, smul_zero, integral_zero]

end UnforcedLeray.Short.PartI
