import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTestBounds

/-!
# Part II-b, task `PartII-b:T15/2/12`: limit of the square term in the logarithmic chart

Source of record: `the November 2 reference manuscript`, lines 1975-1979 (the weak
product rule in the `H_2` measure, log chart `s = e^t`). The target is the Prop `LogSquareLimit`
(`Sub/T15_2.lean`), proved unchanged.

Proof outline. For `u ∈ L²(logMeas c)` and a `LogTest ψ`, the integrand
`((ψ(t - h, y) - ψ(t, y))/h) ‖u‖²` is dominated along `𝓝[≠] 0` by `C ‖u‖²`, where `C` bounds
`|cpd 0 ψ|` (`logTestBounds`), by the mean value inequality along the first coordinate. It converges
pointwise to `-(cpd 0 ψ) ‖u‖²`, since `t ↦ ψ(t, y)` has derivative `cpd 0 ψ (t, y)`. Dominated
convergence (`tendsto_integral_filter_of_dominated_convergence`) finishes the proof.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Calculus along the first coordinate -/

/-- Derivative of `r ↦ ψ(r, y)` at `s` is `cpd 0 ψ (s, y)`. -/
theorem logSquare_hasDerivAt {ψ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) (y : ℝ × ℝ) :
    HasDerivAt (fun r : ℝ => ψ (r, y)) (cpd 0 ψ (s, y)) s := by
  have hd : DifferentiableAt ℝ ψ (s, y) := (hψ.differentiable (by simp)).differentiableAt
  have hl : HasDerivAt (fun r : ℝ => ((r, y) : Coord)) (cdir 0) s := by
    have h1 : HasDerivAt (fun r : ℝ => r) 1 s := hasDerivAt_id' s
    have h2 : HasDerivAt (fun _ : ℝ => y) 0 s := hasDerivAt_const _ _
    have h3 := h1.prodMk h2
    rw [show cdir 0 = (1, 0) by simp [cdir]]
    exact h3
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq s hl rfl

/-- Mean value bound for the first-coordinate difference quotient. -/
theorem logSquare_quot_bound {ψ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ) {C : ℝ}
    (hC : ∀ x : Coord, |cpd 0 ψ x| ≤ C) (x : Coord) {h : ℝ} (hh : h ≠ 0) :
    |(ψ (x.1 - h, x.2) - ψ x) / h| ≤ C := by
  have hmvt : ‖ψ (x.1 - h, x.2) - ψ (x.1, x.2)‖ ≤ C * ‖(x.1 - h) - x.1‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le (f := fun r : ℝ => ψ (r, x.2))
      (s := univ) (fun s _ => (logSquare_hasDerivAt hψ s x.2).differentiableAt) ?_
      convex_univ (mem_univ _) (mem_univ _)
    intro s _
    rw [(logSquare_hasDerivAt hψ s x.2).deriv, Real.norm_eq_abs]
    exact hC (s, x.2)
  have hrw : (x.1 - h) - x.1 = -h := by ring
  rw [hrw] at hmvt
  simp only [norm_neg, Real.norm_eq_abs] at hmvt
  rw [abs_div, div_le_iff₀ (abs_pos.2 hh)]
  exact hmvt

/-- Pointwise limit of the difference quotient in the first coordinate. -/
theorem logSquare_pointwise {ψ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : Coord) :
    Tendsto (fun h : ℝ => (ψ (x.1 - h, x.2) - ψ x) / h) (𝓝[≠] 0) (𝓝 (-cpd 0 ψ x)) := by
  have hg : HasDerivAt (fun r : ℝ => ψ (r, x.2)) (cpd 0 ψ x) (x.1 - 0) := by
    rw [sub_zero]
    exact logSquare_hasDerivAt hψ x.1 x.2
  have hf : HasDerivAt (fun h : ℝ => x.1 - h) (-1) 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_sub x.1
  have hcomp : HasDerivAt ((fun r : ℝ => ψ (r, x.2)) ∘ (fun h : ℝ => x.1 - h))
      (cpd 0 ψ x * (-1)) 0 :=
    HasDerivAt.comp_of_eq (0 : ℝ) hg hf rfl
  have hsl := hasDerivAt_iff_tendsto_slope_zero.1 hcomp
  have key : ∀ t : ℝ,
      t⁻¹ • (((fun r : ℝ => ψ (r, x.2)) ∘ (fun h : ℝ => x.1 - h)) (0 + t) -
        ((fun r : ℝ => ψ (r, x.2)) ∘ (fun h : ℝ => x.1 - h)) 0)
        = (ψ (x.1 - t, x.2) - ψ x) / t := by
    intro t
    simp [Function.comp_apply, smul_eq_mul, div_eq_inv_mul]
  have hlim := Tendsto.congr key hsl
  rw [mul_neg_one] at hlim
  exact hlim

/-! ## Assembly -/

/-- **Leaf `PartII-b:T15/2/12`** (limit of the square term). For `u ∈ L²(logMeas c)` and a
`LogTest ψ`, `∫ ((ψ(t - h, y) - ψ(t, y))/h) ‖u‖² dλ → -∫ ∂_tψ ‖u‖² dλ` as `h → 0`, `h ≠ 0`. -/
theorem logSquareLimit : UnforcedLeray.Short.IIb.LogSquareLimit := by
  intro c u ψ hc hu hψ
  have hB : UnforcedLeray.Short.IIb.LogTestBounds := logTestBounds
  obtain ⟨_, ⟨C, hC⟩, _⟩ := hB c ψ hc hψ
  have hψs : ContDiff ℝ ∞ ψ := hψ.smooth
  have hψc : Continuous ψ := hψs.continuous
  have hsq : Integrable (fun x : Coord => ‖u x‖ ^ 2) (logMeas c) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  rw [← integral_neg]
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun (h : ℝ) (x : Coord) => ((ψ (x.1 - h, x.2) - ψ x) / h : ℝ) * ‖u x‖ ^ 2)
    (f := fun x : Coord => -(cpd 0 ψ x * ‖u x‖ ^ 2))
    (fun x : Coord => C * ‖u x‖ ^ 2) ?_ ?_ (hsq.const_mul C) ?_
  · refine Filter.Eventually.of_forall (fun h : ℝ => ?_)
    have hcont : Continuous (fun x : Coord => (ψ (x.1 - h, x.2) - ψ x) / h) := by
      refine Continuous.div_const ?_ h
      refine Continuous.sub ?_ hψc
      exact hψc.comp (by fun_prop)
    exact hcont.aestronglyMeasurable.mul hsq.aestronglyMeasurable
  · have hne : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ≠ 0 := eventually_mem_nhdsWithin
    filter_upwards [hne] with h hh
    refine ae_of_all _ (fun x => ?_)
    show ‖((ψ (x.1 - h, x.2) - ψ x) / h : ℝ) * ‖u x‖ ^ 2‖ ≤ C * ‖u x‖ ^ 2
    have hb := logSquare_quot_bound hψs hC x hh
    rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u x‖ ^ 2), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  · refine ae_of_all _ (fun x => ?_)
    have hlim := (logSquare_pointwise hψs x).mul_const (‖u x‖ ^ 2)
    rw [neg_mul] at hlim
    exact hlim

end UnforcedLeray.Short.IIb
