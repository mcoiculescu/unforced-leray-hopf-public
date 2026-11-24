import UnforcedLeray.Short.PartI.Sub.S04
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# `BiotSavartDerivFormula`: the Biot-Savart velocity is `C¹` and differentiates under the integral

Source of record: `the November 2 reference manuscript`, lines 788-803.
For `q` in the Gaussian class, each component `B0009.biotSavart q i` is `C¹` and
`∂_v (K_i q) = K_i (∂_v q)`.

Route: `K_i q (y) = ∫ K_i(t) q(y - t) dt` (`bsd_biotSavart_eq`). Differentiate under the integral
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`) with the dominating function
`|K_i(t)| · sup_{‖x‖ ≤ M} |∇q(x - t)|`, which is bounded by `|K_i(t)| · C · exp(-‖t‖²/16)`
(`bsd_gauss_shift`, `bsd_fderiv_gauss`). The kernel is `L¹` near `0` and bounded away from `0`,
so `|K_i| · exp(-‖t‖²/16)` is integrable (`bsd_kernel_gauss_int`). Continuity of the derivative
follows from `continuousAt_of_dominated` with the same bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-! ### Elementary Gaussian estimates -/

theorem bsd_sq_lower (a s M : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) (hM : 0 ≤ M) (h : s - M ≤ a) :
    s ^ 2 / 2 - M ^ 2 ≤ a ^ 2 := by
  rcases le_total s M with hsM | hsM
  · nlinarith [mul_nonneg (sub_nonneg.2 hsM) (add_nonneg hM hs), sq_nonneg s, sq_nonneg a]
  · have h2 : 0 ≤ a + (s - M) := by linarith
    nlinarith [mul_nonneg (sub_nonneg.2 h) h2, sq_nonneg (s - 2 * M)]

/-- Shifting the Gaussian: if `‖y‖ ≤ M` then `exp(-‖y - t‖²/8) ≤ exp(M²/8) exp(-‖t‖²/16)`. -/
theorem bsd_gauss_shift (y t : ℂ) (M : ℝ) (hM : ‖y‖ ≤ M) :
    Real.exp (-(‖y - t‖ ^ 2) / 8) ≤ Real.exp (M ^ 2 / 8) * Real.exp (-(‖t‖ ^ 2) / 16) := by
  have hM0 : 0 ≤ M := (norm_nonneg y).trans hM
  have h1 : ‖t‖ - M ≤ ‖y - t‖ := by
    have h := norm_sub_norm_le t y
    rw [norm_sub_rev t y] at h
    linarith
  have h2 := bsd_sq_lower ‖y - t‖ ‖t‖ M (norm_nonneg _) (norm_nonneg _) hM0 h1
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  linarith

/-- Polynomial times Gaussian is dominated by a pure Gaussian. -/
theorem bsd_poly_gauss (C : ℝ) (N : ℕ) (a : ℝ) (ha : 0 ≤ a) :
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

theorem bsd_bound_of_iter {g : ℂ → ℝ}
    (hg : ∃ C : ℝ, ∃ N : ℕ, ∀ y, g y ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, g y ≤ K * Real.exp (-(‖y‖ ^ 2) / 8) := by
  obtain ⟨C, N, hC⟩ := hg
  refine ⟨|C| * Real.exp (2 * (N : ℝ) ^ 2), by positivity, fun y => ?_⟩
  calc g y ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4) := hC y
    _ ≤ |C| * Real.exp (2 * (N : ℝ) ^ 2) * Real.exp (-(‖y‖ ^ 2) / 8) :=
        bsd_poly_gauss C N ‖y‖ (norm_nonneg y)

theorem bsd_fderiv_norm_eq (q : ℂ → ℂ) (w : ℂ) :
    ‖fderiv ℝ q w‖ = ‖iteratedFDeriv ℝ 1 q w‖ := by
  have h : ‖iteratedFDeriv ℝ 0 (fderiv ℝ q) w‖ = ‖iteratedFDeriv ℝ (0 + 1) q w‖ :=
    norm_iteratedFDeriv_fderiv
  rw [norm_iteratedFDeriv_zero] at h
  simpa using h

/-- Gaussian bound on `∇q` from the `k = 1` Gaussian bound. -/
theorem bsd_fderiv_gauss {q : ℂ → ℂ}
    (hqb : ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y,
      ‖iteratedFDeriv ℝ k q y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖fderiv ℝ q y‖ ≤ K * Real.exp (-(‖y‖ ^ 2) / 8) := by
  obtain ⟨C, N, hC⟩ := hqb 1
  refine bsd_bound_of_iter (g := fun y => ‖fderiv ℝ q y‖) ⟨C, N, fun y => ?_⟩
  show ‖fderiv ℝ q y‖ ≤ _
  rw [bsd_fderiv_norm_eq]
  exact hC y

/-- Gaussian bound on `q` from the `k = 0` Gaussian bound. -/
theorem bsd_q_gauss {q : ℂ → ℂ}
    (hqb : ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y,
      ‖iteratedFDeriv ℝ k q y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖q y‖ ≤ K * Real.exp (-(‖y‖ ^ 2) / 8) := by
  obtain ⟨C, N, hC⟩ := hqb 0
  refine bsd_bound_of_iter (g := fun y => ‖q y‖) ⟨C, N, fun y => ?_⟩
  show ‖q y‖ ≤ _
  have h := hC y
  rwa [norm_iteratedFDeriv_zero] at h

/-- The Gaussian `exp(-‖t‖²/16)` is integrable on `ℂ`. -/
theorem bsd_gauss_int : Integrable (fun t : ℂ => Real.exp (-(‖t‖ ^ 2) / 16)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ)
    (b := ((1 / 16 : ℝ) : ℂ)) (by norm_num) 0 0).re
  change Integrable (fun x : ℂ => (Complex.exp
    (-((1 / 16 : ℝ) : ℂ) * ‖x‖ ^ 2 + 0 * inner ℝ (0 : ℂ) x)).re) at h
  have h2 : Integrable (fun x : ℂ => Real.exp (-(1 / 16 : ℝ) * ‖x‖ ^ 2)) := by
    simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re] using h
  refine h2.congr (ae_of_all _ fun x => ?_)
  congr 1
  ring

/-! ### Integrability of the kernel against the Gaussian -/

theorem bsd_kernel_pointwise (i : Fin 2) (t : ℂ) :
    ‖‖B0009.kernel i t‖ * Real.exp (-(‖t‖ ^ 2) / 16)‖ ≤
      (2 * Real.pi)⁻¹ * Real.exp (-(‖t‖ ^ 2) / 16) +
        (Metric.ball (0 : ℂ) 1).indicator (fun s => ‖B0009.kernel i s‖) t := by
  have hE0 : 0 ≤ Real.exp (-(‖t‖ ^ 2) / 16) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(‖t‖ ^ 2) / 16) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith [sq_nonneg ‖t‖])
  have hk := norm_nonneg (B0009.kernel i t)
  rw [Real.norm_of_nonneg (mul_nonneg hk hE0)]
  by_cases ht : t ∈ Metric.ball (0 : ℂ) 1
  · simp only [Set.indicator_of_mem ht]
    have h1 : ‖B0009.kernel i t‖ * Real.exp (-(‖t‖ ^ 2) / 16) ≤ ‖B0009.kernel i t‖ * 1 :=
      mul_le_mul_of_nonneg_left hE1 hk
    have h2 : 0 ≤ (2 * Real.pi)⁻¹ * Real.exp (-(‖t‖ ^ 2) / 16) :=
      mul_nonneg (by positivity) hE0
    linarith
  · simp only [Set.indicator_of_notMem ht, add_zero]
    have h1 : ‖B0009.kernel i t‖ ≤ (2 * Real.pi)⁻¹ :=
      B0009.norm_kernel_le_of_notMem_ball i ht
    exact mul_le_mul_of_nonneg_right h1 hE0

theorem bsd_kernel_gauss_int (i : Fin 2) :
    Integrable (fun t : ℂ => ‖B0009.kernel i t‖ * Real.exp (-(‖t‖ ^ 2) / 16)) := by
  have hGm : Measurable (fun t : ℂ => Real.exp (-(‖t‖ ^ 2) / 16)) := by fun_prop
  have hg : Integrable (fun t : ℂ => (2 * Real.pi)⁻¹ * Real.exp (-(‖t‖ ^ 2) / 16) +
      (Metric.ball (0 : ℂ) 1).indicator (fun s => ‖B0009.kernel i s‖) t) :=
    (bsd_gauss_int.const_mul _).add
      ((integrable_indicator_iff measurableSet_ball).2 (Integrable.norm (B0009.integrableOn_kernel_ball i)))
  exact Integrable.mono' hg
    (((B0009.measurable_kernel i).norm.mul hGm).aestronglyMeasurable)
    (ae_of_all _ (bsd_kernel_pointwise i))

/-! ### Domination of the integrand and of its `y`-derivative -/

theorem bsd_F'_dom {q : ℂ → ℂ} (i : Fin 2) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ w, ‖fderiv ℝ q w‖ ≤ K * Real.exp (-(‖w‖ ^ 2) / 8)) (M : ℝ) {x : ℂ}
    (hx : ‖x‖ ≤ M) (a : ℂ) :
    ‖B0009.kernel i a • fderiv ℝ q (x - a)‖ ≤
      (K * Real.exp (M ^ 2 / 8)) * (‖B0009.kernel i a‖ * Real.exp (-(‖a‖ ^ 2) / 16)) := by
  have hE := bsd_gauss_shift x a M hx
  have h1 := hK (x - a)
  have hn := norm_nonneg (B0009.kernel i a)
  rw [norm_smul]
  calc ‖B0009.kernel i a‖ * ‖fderiv ℝ q (x - a)‖
      ≤ ‖B0009.kernel i a‖ * (K * Real.exp (-(‖x - a‖ ^ 2) / 8)) :=
        mul_le_mul_of_nonneg_left h1 hn
    _ ≤ ‖B0009.kernel i a‖ * (K * (Real.exp (M ^ 2 / 8) * Real.exp (-(‖a‖ ^ 2) / 16))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hK0) hn
    _ = (K * Real.exp (M ^ 2 / 8)) * (‖B0009.kernel i a‖ * Real.exp (-(‖a‖ ^ 2) / 16)) := by ring

theorem bsd_F_dom {q : ℂ → ℂ} (i : Fin 2) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ w, ‖q w‖ ≤ K * Real.exp (-(‖w‖ ^ 2) / 8)) (M : ℝ) {x : ℂ}
    (hx : ‖x‖ ≤ M) (a : ℂ) :
    ‖B0009.kernel i a * q (x - a)‖ ≤
      (K * Real.exp (M ^ 2 / 8)) * (‖B0009.kernel i a‖ * Real.exp (-(‖a‖ ^ 2) / 16)) := by
  have hE := bsd_gauss_shift x a M hx
  have h1 := hK (x - a)
  have hn := norm_nonneg (B0009.kernel i a)
  rw [norm_mul]
  calc ‖B0009.kernel i a‖ * ‖q (x - a)‖
      ≤ ‖B0009.kernel i a‖ * (K * Real.exp (-(‖x - a‖ ^ 2) / 8)) :=
        mul_le_mul_of_nonneg_left h1 hn
    _ ≤ ‖B0009.kernel i a‖ * (K * (Real.exp (M ^ 2 / 8) * Real.exp (-(‖a‖ ^ 2) / 16))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hK0) hn
    _ = (K * Real.exp (M ^ 2 / 8)) * (‖B0009.kernel i a‖ * Real.exp (-(‖a‖ ^ 2) / 16)) := by ring

/-- On the unit ball around `x0`, the derivative integrand is dominated by a fixed integrable
function of `a`. -/
theorem bsd_ball_dom {q : ℂ → ℂ} (i : Fin 2) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ w, ‖fderiv ℝ q w‖ ≤ K * Real.exp (-(‖w‖ ^ 2) / 8)) (x0 : ℂ) {x : ℂ}
    (hx : x ∈ Metric.ball x0 1) (a : ℂ) :
    ‖B0009.kernel i a • fderiv ℝ q (x - a)‖ ≤
      (K * Real.exp ((‖x0‖ + 1) ^ 2 / 8)) * (‖B0009.kernel i a‖ * Real.exp (-(‖a‖ ^ 2) / 16)) := by
  have hxM : ‖x‖ ≤ ‖x0‖ + 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have h := norm_sub_norm_le x x0
    linarith
  exact bsd_F'_dom i hK0 hK (‖x0‖ + 1) hxM a

/-- The derivative integrand `a ↦ K_i(a) ∇q(x - a)` is integrable. -/
theorem bsd_F'_integrable {q : ℂ → ℂ} (hfdc : Continuous (fderiv ℝ q)) (i : Fin 2) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ w, ‖fderiv ℝ q w‖ ≤ K * Real.exp (-(‖w‖ ^ 2) / 8)) (x : ℂ) :
    Integrable (fun a => B0009.kernel i a • fderiv ℝ q (x - a)) := by
  refine Integrable.mono' ((bsd_kernel_gauss_int i).const_mul (K * Real.exp (‖x‖ ^ 2 / 8))) ?_
    (ae_of_all _ fun a => bsd_F'_dom i hK0 hK ‖x‖ le_rfl a)
  exact ((B0009.measurable_kernel i).smul
    (hfdc.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable

/-- Pointwise derivative of `a`-translated `q` in the Gaussian class. -/
theorem bsd_hasFDerivAt_aux {q : ℂ → ℂ} (hqc : ContDiff ℝ ∞ q) (i : Fin 2) (a x : ℂ) :
    HasFDerivAt (fun y => B0009.kernel i a * q (y - a))
      (B0009.kernel i a • fderiv ℝ q (x - a)) x := by
  have hq_d : HasFDerivAt q (fderiv ℝ q (x - a)) (x - a) :=
    ((hqc.differentiable (by simp)) (x - a)).hasFDerivAt
  have hsub : HasFDerivAt (fun y : ℂ => y - a) (ContinuousLinearMap.id ℝ ℂ) x :=
    (hasFDerivAt_id x).sub_const a
  have hcomp := hq_d.comp x hsub
  have := hcomp.const_mul (B0009.kernel i a)
  rw [ContinuousLinearMap.comp_id] at this
  exact this

/-! ### Biot-Savart as a translated convolution -/

theorem bsd_biotSavart_eq (g : ℂ → ℂ) (i : Fin 2) (y : ℂ) :
    B0009.biotSavart g i y = ∫ t, B0009.kernel i t * g (y - t) := by
  rw [B0009.biotSavart_apply]
  have h := integral_sub_left_eq_self (fun t => B0009.kernel i t * g (y - t)) volume y
  simp only [sub_sub_cancel] at h
  exact h

/-! ### The main statement -/

theorem biotSavartDerivFormula : BiotSavartDerivFormula := by
  unfold BiotSavartDerivFormula
  intro q hG i
  unfold PlanarGaussianClass at hG
  obtain ⟨hqc, hqb⟩ := hG
  have hfdc : Continuous (fderiv ℝ q) := (hqc.fderiv_right (m := ∞) (by simp)).continuous
  have hqm : Measurable q := hqc.continuous.measurable
  obtain ⟨K1, hK10, hK1⟩ := bsd_fderiv_gauss hqb
  obtain ⟨K0, hK00, hK0⟩ := bsd_q_gauss hqb
  have hBfun : B0009.biotSavart q i = fun y => ∫ a, B0009.kernel i a * q (y - a) :=
    funext fun y => bsd_biotSavart_eq q i y
  -- the derivative at each point, by differentiation under the integral
  have hderiv : ∀ x0 : ℂ, HasFDerivAt (B0009.biotSavart q i)
      (∫ a, B0009.kernel i a • fderiv ℝ q (x0 - a)) x0 := by
    intro x0
    rw [hBfun]
    have hFm : ∀ᶠ y in 𝓝 x0,
        AEStronglyMeasurable (fun a => B0009.kernel i a * q (y - a)) volume :=
      Filter.Eventually.of_forall fun y =>
        ((B0009.measurable_kernel i).mul (hqm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    have hFi : Integrable (fun a => B0009.kernel i a * q (x0 - a)) volume :=
      Integrable.mono' ((bsd_kernel_gauss_int i).const_mul (K0 * Real.exp (‖x0‖ ^ 2 / 8)))
        ((B0009.measurable_kernel i).mul (hqm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
        (ae_of_all _ fun a => bsd_F_dom (x := x0) i hK00 hK0 ‖x0‖ le_rfl a)
    have hF'm : AEStronglyMeasurable (fun a => B0009.kernel i a • fderiv ℝ q (x0 - a)) volume :=
      (bsd_F'_integrable hfdc i hK10 hK1 x0).aestronglyMeasurable
    have hb : ∀ᵐ a ∂volume, ∀ x ∈ Metric.ball x0 1,
        ‖B0009.kernel i a • fderiv ℝ q (x - a)‖ ≤
          (K1 * Real.exp ((‖x0‖ + 1) ^ 2 / 8)) *
            (‖B0009.kernel i a‖ * Real.exp (-(‖a‖ ^ 2) / 16)) :=
      ae_of_all _ fun a x hx => bsd_ball_dom i hK10 hK1 x0 hx a
    have hbi : Integrable (fun a => (K1 * Real.exp ((‖x0‖ + 1) ^ 2 / 8)) *
        (‖B0009.kernel i a‖ * Real.exp (-(‖a‖ ^ 2) / 16))) volume :=
      (bsd_kernel_gauss_int i).const_mul _
    have hd : ∀ᵐ a ∂volume, ∀ x ∈ Metric.ball x0 1,
        HasFDerivAt (fun y => B0009.kernel i a * q (y - a))
          (B0009.kernel i a • fderiv ℝ q (x - a)) x :=
      ae_of_all _ fun a x _ => bsd_hasFDerivAt_aux hqc i a x
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun y a => B0009.kernel i a * q (y - a))
      (F' := fun y a => B0009.kernel i a • fderiv ℝ q (y - a))
      (bound := fun a => (K1 * Real.exp ((‖x0‖ + 1) ^ 2 / 8)) *
        (‖B0009.kernel i a‖ * Real.exp (-(‖a‖ ^ 2) / 16)))
      (Metric.ball_mem_nhds x0 one_pos) hFm hFi hF'm hb hbi hd
  have hfd : ∀ x0 : ℂ, fderiv ℝ (B0009.biotSavart q i) x0 =
      ∫ a, B0009.kernel i a • fderiv ℝ q (x0 - a) :=
    fun x0 => (hderiv x0).fderiv
  have hfd_eq : fderiv ℝ (B0009.biotSavart q i) =
      fun x0 => ∫ a, B0009.kernel i a • fderiv ℝ q (x0 - a) :=
    funext hfd
  have hdiff : Differentiable ℝ (B0009.biotSavart q i) := fun x0 => (hderiv x0).differentiableAt
  -- continuity of the derivative, by dominated convergence at each point
  have hcont : Continuous (fderiv ℝ (B0009.biotSavart q i)) := by
    rw [hfd_eq, continuous_iff_continuousAt]
    intro x0
    refine continuousAt_of_dominated
      (F := fun x a => B0009.kernel i a • fderiv ℝ q (x - a))
      (bound := fun a => (K1 * Real.exp ((‖x0‖ + 1) ^ 2 / 8)) *
        (‖B0009.kernel i a‖ * Real.exp (-(‖a‖ ^ 2) / 16))) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x =>
        (bsd_F'_integrable hfdc i hK10 hK1 x).aestronglyMeasurable
    · have hev : ∀ᶠ x in 𝓝 x0, x ∈ Metric.ball x0 1 := Metric.ball_mem_nhds x0 one_pos
      exact hev.mono fun x hx => ae_of_all _ fun a => bsd_ball_dom i hK10 hK1 x0 hx a
    · exact (bsd_kernel_gauss_int i).const_mul _
    · refine ae_of_all _ fun a => ?_
      have hsub : Continuous (fun x : ℂ => x - a) := continuous_id.sub continuous_const
      have hc : Continuous (fun x : ℂ => fderiv ℝ q (x - a)) := hfdc.comp hsub
      exact (hc.const_smul (B0009.kernel i a)).continuousAt
  refine ⟨?_, ?_⟩
  · exact contDiff_one_iff_fderiv.2 ⟨hdiff, hcont⟩
  · intro y v
    rw [hfd y, ContinuousLinearMap.integral_apply (bsd_F'_integrable hfdc i hK10 hK1 y) v,
      bsd_biotSavart_eq]
    congr 1
