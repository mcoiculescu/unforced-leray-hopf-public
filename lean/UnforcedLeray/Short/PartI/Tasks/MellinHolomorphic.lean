import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Part I, task `PartI:C13`: holomorphy of the Mellin-type integral on the half plane

Source of record: `the November 2 reference manuscript`, lines 1164-1170
(absolute convergence on `Re μ > -3/2` permits differentiation under the integral sign,
including every logarithmic factor, on compact subsets of the half plane).

Proof. Fix `μ0` with `-(3/2) < Re μ0`, put `R = Re μ0` and `r = (R + 3/2)/3 > 0`. For `x` in the
ball of radius `r` about `μ0` the exponent `Re x + 1/2` lies in `(R + 1/2 - r, R + 1/2 + r)`.
For `θ > 0` and such an exponent, `θ^x |log θ| ≤ (θ^p + θ^q)/r` with `p = R + 1/2 - 2r` and
`q = R + 1/2 + 2r` (two cases `θ ≤ 1`, `1 ≤ θ`, using `log t ≤ t^r / r`). The exponents `p`,
`q` are `> -1`, so the hypothesis `hm` gives integrability of `θ^p ‖m θ‖` and `θ^q ‖m θ‖`;
these dominate the derivative on the ball, and `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(over `𝕜 = ℂ`) gives complex differentiability at `μ0`. Finally `DifferentiableOn.analyticOnNhd`
on the open half plane.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology

namespace UnforcedLeray.Short.PartI

/-- Elementary bound: for `r > 0`, `θ > 0`, `p ≤ x - r` and `x + r ≤ q`,
`θ ^ x * |log θ| ≤ (θ ^ p + θ ^ q) / r`. -/
theorem rpow_mul_abs_log_le {r θ x p q : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hp : p ≤ x - r)
    (hq : x + r ≤ q) : θ ^ x * |Real.log θ| ≤ (θ ^ p + θ ^ q) / r := by
  rcases le_total θ 1 with hθ1 | hθ1
  · have hlog : |Real.log θ| = Real.log θ⁻¹ := by
      rw [Real.log_inv, abs_of_nonpos (Real.log_nonpos hθ.le hθ1)]
    have h1 : Real.log θ⁻¹ ≤ (θ⁻¹) ^ r / r := Real.log_le_rpow_div (inv_nonneg.2 hθ.le) hr
    have h2 : θ ^ x * (θ⁻¹) ^ r = θ ^ (x - r) := by
      rw [Real.inv_rpow hθ.le, Real.rpow_sub hθ, div_eq_mul_inv]
    have h3 : θ ^ (x - r) ≤ θ ^ p := Real.rpow_le_rpow_of_exponent_ge hθ hθ1 hp
    have h4 : 0 ≤ θ ^ p := Real.rpow_nonneg hθ.le p
    have h5 : 0 ≤ θ ^ q := Real.rpow_nonneg hθ.le q
    calc θ ^ x * |Real.log θ| = θ ^ x * Real.log θ⁻¹ := by rw [hlog]
      _ ≤ θ ^ x * ((θ⁻¹) ^ r / r) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hθ.le x)
      _ = θ ^ (x - r) / r := by rw [← h2]; ring
      _ ≤ (θ ^ p + θ ^ q) / r := (div_le_div_iff_of_pos_right hr).2 (by linarith)
  · have hlog : |Real.log θ| = Real.log θ := abs_of_nonneg (Real.log_nonneg hθ1)
    have h1 : Real.log θ ≤ θ ^ r / r := Real.log_le_rpow_div hθ.le hr
    have h2 : θ ^ x * θ ^ r = θ ^ (x + r) := (Real.rpow_add hθ x r).symm
    have h3 : θ ^ (x + r) ≤ θ ^ q := Real.rpow_le_rpow_of_exponent_le hθ1 hq
    have h4 : 0 ≤ θ ^ p := Real.rpow_nonneg hθ.le p
    calc θ ^ x * |Real.log θ| = θ ^ x * Real.log θ := by rw [hlog]
      _ ≤ θ ^ x * (θ ^ r / r) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hθ.le x)
      _ = (θ ^ x * θ ^ r) / r := by ring
      _ = θ ^ (x + r) / r := by rw [h2]
      _ ≤ (θ ^ p + θ ^ q) / r := (div_le_div_iff_of_pos_right hr).2 (by linarith)

/-- **`PartI:C13`** (source lines 1164-1170): if `m` is measurable and `θ ↦ θ^(μ+1/2) m θ` is
integrable on `(0, ∞)` for every `μ` with `Re μ > -3/2`, then `μ ↦ ∫_0^∞ θ^(μ+1/2) m θ dθ` is
analytic on the half plane `Re μ > -3/2`. -/
theorem mellin_analyticOnNhd {m : ℝ → ℂ} (hm : ∀ μ : ℂ, -(3/2) < μ.re → IntegrableOn (fun θ : ℝ => (θ:ℂ)^(μ+1/2) * m θ) (Set.Ioi 0)) (hmeas : AEStronglyMeasurable m volume) : AnalyticOnNhd ℂ (fun μ => ∫ θ in Set.Ioi (0:ℝ), (θ:ℂ)^(μ+1/2) * m θ) {μ : ℂ | -(3/2) < μ.re} := by
  -- integrability of `θ ^ t * ‖m θ‖` for real exponents `t > -1`
  have hint : ∀ t : ℝ, -1 < t → IntegrableOn (fun θ : ℝ => θ ^ t * ‖m θ‖) (Set.Ioi 0) := by
    intro t ht
    have hexp : ((t - 1/2 : ℝ) : ℂ) + 1/2 = (t : ℂ) := by push_cast; ring
    have h : IntegrableOn (fun θ : ℝ => ‖(θ:ℂ)^(t:ℂ) * m θ‖) (Set.Ioi 0) := by
      have h0 := (hm ((t - 1/2 : ℝ) : ℂ) (by rw [Complex.ofReal_re]; linarith)).norm
      simp only [hexp] at h0
      exact h0
    refine IntegrableOn.congr_fun h (fun θ hθ => ?_) measurableSet_Ioi
    have hθ' : (0:ℝ) < θ := hθ
    show ‖(θ:ℂ)^(t:ℂ) * m θ‖ = θ ^ t * ‖m θ‖
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hθ', Complex.ofReal_re]
  have hderiv : ∀ μ0 : ℂ, -(3/2) < μ0.re →
      HasDerivAt (fun μ : ℂ => ∫ θ in Set.Ioi (0:ℝ), (θ:ℂ)^(μ+1/2) * m θ)
        (∫ θ in Set.Ioi (0:ℝ), (θ:ℂ)^(μ0+1/2) * ((Real.log θ : ℝ) : ℂ) * m θ) μ0 := by
    intro μ0 h0
    obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = (μ0.re + 3/2) / 3 := ⟨_, rfl⟩
    have hr : 0 < r := by rw [hr_def]; linarith
    have hR3 : 3 * r = μ0.re + 3/2 := by rw [hr_def]; ring
    have hp : -1 < μ0.re - 2 * r + 1/2 := by linarith
    have hq : -1 < μ0.re + 2 * r + 1/2 := by linarith
    have hball : Metric.ball μ0 r ∈ 𝓝 μ0 := Metric.ball_mem_nhds μ0 hr
    have hre_ball : ∀ x ∈ Metric.ball μ0 r, μ0.re - r < x.re ∧ x.re < μ0.re + r := by
      intro x hx
      have hd : ‖x - μ0‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hx
      have h1 := Complex.abs_re_le_norm (x - μ0)
      rw [Complex.sub_re] at h1
      have h2 := abs_lt.1 (lt_of_le_of_lt h1 hd)
      constructor <;> linarith [h2.1, h2.2]
    have hexpre : ∀ x : ℂ, (x + 1/2 : ℂ).re = x.re + 1/2 := by
      intro x
      rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.add_re, Complex.ofReal_re]
    -- pointwise complex derivative in the parameter
    have hpt : ∀ θ : ℝ, 0 < θ → ∀ x : ℂ,
        HasDerivAt (fun z : ℂ => (θ:ℂ)^(z+1/2) * m θ)
          ((θ:ℂ)^(x+1/2) * ((Real.log θ : ℝ) : ℂ) * m θ) x := by
      intro θ hθ x
      have hθC : (θ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hθ.ne'
      have h1 : HasDerivAt (fun z : ℂ => (θ:ℂ)^(z+1/2))
          ((θ:ℂ)^(x+1/2) * Complex.log (θ:ℂ) * 1) x :=
        ((hasDerivAt_id' x).add_const (1/2 : ℂ)).const_cpow (Or.inl hθC)
      refine (h1.mul_const (m θ)).congr_deriv ?_
      rw [← Complex.ofReal_log hθ.le]
      ring
    -- the dominating bound on the ball
    have hF'bd : ∀ θ : ℝ, 0 < θ → ∀ x ∈ Metric.ball μ0 r,
        ‖(θ:ℂ)^(x+1/2) * ((Real.log θ : ℝ) : ℂ) * m θ‖ ≤
          (θ ^ (μ0.re - 2 * r + 1/2) * ‖m θ‖ + θ ^ (μ0.re + 2 * r + 1/2) * ‖m θ‖) / r := by
      intro θ hθ x hx
      obtain ⟨hx1, hx2⟩ := hre_ball x hx
      have key := rpow_mul_abs_log_le (x := x.re + 1/2) (p := μ0.re - 2 * r + 1/2)
        (q := μ0.re + 2 * r + 1/2) hr hθ (by linarith) (by linarith)
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hθ, hexpre x,
        Complex.norm_real, Real.norm_eq_abs]
      calc θ ^ (x.re + 1/2) * |Real.log θ| * ‖m θ‖
          ≤ ((θ ^ (μ0.re - 2 * r + 1/2) + θ ^ (μ0.re + 2 * r + 1/2)) / r) * ‖m θ‖ :=
            mul_le_mul_of_nonneg_right key (norm_nonneg _)
        _ = (θ ^ (μ0.re - 2 * r + 1/2) * ‖m θ‖ + θ ^ (μ0.re + 2 * r + 1/2) * ‖m θ‖) / r := by
            ring
    have hF_meas : ∀ᶠ x in 𝓝 μ0,
        AEStronglyMeasurable (fun θ : ℝ => (θ:ℂ)^(x+1/2) * m θ)
          (volume.restrict (Set.Ioi (0:ℝ))) :=
      Filter.eventually_of_mem hball fun x hx =>
        (hm x (by linarith [(hre_ball x hx).1])).aestronglyMeasurable
    have hF'_meas : AEStronglyMeasurable
        (fun θ : ℝ => (θ:ℂ)^(μ0+1/2) * ((Real.log θ : ℝ) : ℂ) * m θ)
        (volume.restrict (Set.Ioi (0:ℝ))) := by
      have hcont : ContinuousOn (fun θ : ℝ => (θ:ℂ)^(μ0+1/2) * ((Real.log θ : ℝ) : ℂ))
          (Set.Ioi 0) := by
        apply ContinuousOn.mul
        · exact continuousOn_of_forall_continuousAt fun t ht =>
            Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
        · exact Complex.continuous_ofReal.comp_continuousOn
            (Real.continuousOn_log.mono (subset_compl_singleton_iff.mpr self_notMem_Ioi))
      exact (hcont.aestronglyMeasurable measurableSet_Ioi).mul
        (hmeas.restrict (s := Set.Ioi (0:ℝ)))
    have h_bound : ∀ᵐ θ : ℝ ∂(volume.restrict (Set.Ioi (0:ℝ))), ∀ x ∈ Metric.ball μ0 r,
        ‖(θ:ℂ)^(x+1/2) * ((Real.log θ : ℝ) : ℂ) * m θ‖ ≤
          (θ ^ (μ0.re - 2 * r + 1/2) * ‖m θ‖ + θ ^ (μ0.re + 2 * r + 1/2) * ‖m θ‖) / r :=
      (ae_restrict_mem measurableSet_Ioi).mono fun θ hθ x hx => hF'bd θ hθ x hx
    have hbound_int : Integrable
        (fun θ : ℝ => (θ ^ (μ0.re - 2 * r + 1/2) * ‖m θ‖ + θ ^ (μ0.re + 2 * r + 1/2) * ‖m θ‖) / r)
        (volume.restrict (Set.Ioi (0:ℝ))) :=
      ((hint _ hp).add (hint _ hq)).div_const r
    have h_diff : ∀ᵐ θ : ℝ ∂(volume.restrict (Set.Ioi (0:ℝ))), ∀ x ∈ Metric.ball μ0 r,
        HasDerivAt (fun z : ℂ => (θ:ℂ)^(z+1/2) * m θ)
          ((θ:ℂ)^(x+1/2) * ((Real.log θ : ℝ) : ℂ) * m θ) x :=
      (ae_restrict_mem measurableSet_Ioi).mono fun θ hθ x _ => hpt θ hθ x
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (F := fun (μ : ℂ) (θ : ℝ) => (θ:ℂ)^(μ+1/2) * m θ)
      (F' := fun (μ : ℂ) (θ : ℝ) => (θ:ℂ)^(μ+1/2) * ((Real.log θ : ℝ) : ℂ) * m θ)
      (x₀ := μ0)
      (bound := fun θ : ℝ =>
        (θ ^ (μ0.re - 2 * r + 1/2) * ‖m θ‖ + θ ^ (μ0.re + 2 * r + 1/2) * ‖m θ‖) / r)
      hball hF_meas (hm μ0 h0) hF'_meas h_bound hbound_int h_diff
    exact key.2
  have hdiff : DifferentiableOn ℂ
      (fun μ : ℂ => ∫ θ in Set.Ioi (0:ℝ), (θ:ℂ)^(μ+1/2) * m θ) {μ : ℂ | -(3/2) < μ.re} :=
    fun μ hμ => (hderiv μ hμ).differentiableAt.differentiableWithinAt
  exact hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end UnforcedLeray.Short.PartI
