import UnforcedLeray.Lib.HeatR3.Comm
import UnforcedLeray.Lib.Gaussian.Absorb
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The `L^p` generator of the generic heat semigroup (INF04 T4, generic group)


`heatConvK` and `hasDerivAt_heatLp_time` on a general group `G` with a continuous homomorphism
`ι : ℝ^d → G` (decision D17; the setting of `ConvOp`, `LpOp`, `Comm`). Used for the bypass BP5
(the generator of the heat semigroup on `L^p`, B0447–B0450) and for the cylinder heat flow of
INF05 (B0224, B0487).

* `heatConvK ι K u`: convolution of `u : G → E` with a scalar kernel `K` on `ℝ^d` along `ι`,
  `x ↦ ∫ K(y) u(x - ιy) dy` (for `K = G_θ` this is `heatConv`).
* `heatLpK ι hι K u`: the same as an `L^p`-valued Bochner integral `∫ K(y) τ_{ιy}u dy` of
  translates (for `K = G_θ`, `θ > 0`, this is `heatLp`, `heatLp_eq_integral`).
* `gaussDt d θ`: the time derivative `∂_θ G_θ(y) = (|y|²/(4θ²) - d/(2θ)) G_θ(y)`
  (`hasDerivAt_gaussKernel_time`; it equals `ΔG_θ`).
* `hasDerivAt_heatLp_time`: for `1 ≤ p < ∞`, `θ > 0`, `u ∈ L^p`:
  `d/dθ e^{θΔ}u = heatLpK ι hι (gaussDt d θ) u` in the norm of `L^p` (dominated differentiation
  of the `L^p`-valued integral of `heatLp_eq_integral`; translations are isometries).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology Real
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-! ### The time derivative of the Gaussian -/

/-- `∂_θ G_θ(y) = (|y|²/(4θ²) - d/(2θ)) G_θ(y)`. -/
def gaussDt (d : ℕ) (θ : ℝ) (y : Euc d) : ℝ :=
  (‖y‖ ^ 2 / (4 * θ ^ 2) - d / (2 * θ)) * gaussKernel d θ y

theorem continuous_gaussDt (d : ℕ) (θ : ℝ) : Continuous (gaussDt d θ) := by
  unfold gaussDt
  exact ((continuous_norm.pow 2).div_const _ |>.sub continuous_const).mul
    (Gaussian.continuous_gaussKernel θ)

/-- **INF04 T1/T4.** `θ ↦ G_θ(y)` is differentiable at `θ > 0` with derivative `gaussDt d θ y`. -/
theorem hasDerivAt_gaussKernel_time {d : ℕ} {θ : ℝ} (hθ : 0 < θ) (y : Euc d) :
    HasDerivAt (fun s => gaussKernel d s y) (gaussDt d θ y) θ := by
  have h4 : (4 * π * θ) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => (4 * π * s) ^ (-(d : ℝ) / 2))
      (4 * π * (-(d : ℝ) / 2) * (4 * π * θ) ^ (-(d : ℝ) / 2 - 1)) θ := by
    have hl : HasDerivAt (fun s : ℝ => 4 * π * s) (4 * π) θ := by
      simpa using (hasDerivAt_id θ).const_mul (4 * π)
    exact hl.rpow_const (Or.inl h4)
  have hinv : HasDerivAt (fun s : ℝ => (4 * s)⁻¹) (-4 / (4 * θ) ^ 2) θ := by
    have hl : HasDerivAt (fun s : ℝ => 4 * s) 4 θ := by
      simpa using (hasDerivAt_id θ).const_mul (4 : ℝ)
    exact hl.inv (by positivity)
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-‖y‖ ^ 2 / (4 * s)))
      (Real.exp (-‖y‖ ^ 2 / (4 * θ)) * (-‖y‖ ^ 2 * (-4 / (4 * θ) ^ 2))) θ := by
    have h := (hinv.const_mul (-‖y‖ ^ 2)).exp
    simp only [← div_eq_mul_inv] at h
    exact h
  have h := h1.mul h2
  unfold gaussKernel
  refine h.congr_deriv ?_
  unfold gaussDt gaussKernel
  rw [Real.rpow_sub_one h4]
  field_simp
  ring

/-- A uniform Gaussian envelope for `gaussDt` on `θ/2 < s < 2θ`. -/
theorem abs_gaussDt_le {d : ℕ} {θ : ℝ} (hθ : 0 < θ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℝ, θ / 2 < s → s < 2 * θ → ∀ y : Euc d,
      |gaussDt d s y| ≤ A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) := by
  obtain ⟨C₁, hC₁, hC⟩ := Gaussian.rpow_mul_exp_neg_mul_sq_le (m := 2) (b := 1 / (16 * θ))
    (by norm_num) (by positivity)
  refine ⟨(C₁ / θ ^ 2 + d / θ) * (2 * π * θ) ^ (-(d : ℝ) / 2), by positivity,
    fun s hs1 hs2 y => ?_⟩
  have hs : 0 < s := by linarith
  set r := ‖y‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg y
  -- the prefactor
  have hpre : (4 * π * s) ^ (-(d : ℝ) / 2) ≤ (2 * π * θ) ^ (-(d : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Real.pi_pos])
      (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  -- the Gaussian factor
  have hq : 1 / (8 * θ) * r ^ 2 ≤ r ^ 2 / (4 * s) := by
    rw [div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) (by linarith)
  have hexp : Real.exp (-r ^ 2 / (4 * s)) ≤ Real.exp (-(1 / (8 * θ)) * r ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_mul]
    linarith
  have hmono : Real.exp (-(1 / (8 * θ)) * r ^ 2) ≤ Real.exp (-(1 / (16 * θ)) * r ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    have h816 : 1 / (16 * θ) ≤ 1 / (8 * θ) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_right h816 (sq_nonneg r)
  have hsplit : Real.exp (-(1 / (8 * θ)) * r ^ 2) =
      Real.exp (-(1 / (16 * θ) * r ^ 2)) * Real.exp (-(1 / (16 * θ)) * r ^ 2) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hpoly : r ^ 2 * Real.exp (-(1 / (16 * θ) * r ^ 2)) ≤ C₁ := by
    have := hC r hr0
    rwa [show r ^ (2 : ℝ) = r ^ 2 by norm_cast] at this
  have hG : gaussKernel d s y = (4 * π * s) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * s)) := rfl
  have hcoef : |r ^ 2 / (4 * s ^ 2) - d / (2 * s)| ≤ r ^ 2 / θ ^ 2 + d / θ := by
    have h1 : r ^ 2 / (4 * s ^ 2) ≤ r ^ 2 / θ ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have h2 : (d : ℝ) / (2 * s) ≤ d / θ := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg d) hθ
      linarith
    have h3 : 0 ≤ r ^ 2 / (4 * s ^ 2) := by positivity
    have h4 : 0 ≤ (d : ℝ) / (2 * s) := by positivity
    rw [abs_le]; constructor <;> linarith
  have hE0 : 0 ≤ Real.exp (-(1 / (16 * θ)) * r ^ 2) := (Real.exp_pos _).le
  unfold gaussDt
  rw [abs_mul, hG, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * π * s) ^ (-(d : ℝ) / 2) *
    Real.exp (-r ^ 2 / (4 * s)))]
  calc |r ^ 2 / (4 * s ^ 2) - d / (2 * s)| *
        ((4 * π * s) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * s)))
      ≤ (r ^ 2 / θ ^ 2 + d / θ) *
        ((2 * π * θ) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (8 * θ)) * r ^ 2)) := by
        gcongr
    _ = (2 * π * θ) ^ (-(d : ℝ) / 2) * ((r ^ 2 * Real.exp (-(1 / (16 * θ) * r ^ 2))) / θ ^ 2 *
          Real.exp (-(1 / (16 * θ)) * r ^ 2) + d / θ * Real.exp (-(1 / (8 * θ)) * r ^ 2)) := by
        rw [hsplit]; ring
    _ ≤ (2 * π * θ) ^ (-(d : ℝ) / 2) * (C₁ / θ ^ 2 * Real.exp (-(1 / (16 * θ)) * r ^ 2) +
          d / θ * Real.exp (-(1 / (16 * θ)) * r ^ 2)) := by
        have e1 : (r ^ 2 * Real.exp (-(1 / (16 * θ) * r ^ 2))) / θ ^ 2 ≤ C₁ / θ ^ 2 :=
          div_le_div_of_nonneg_right hpoly (by positivity)
        have e2 : d / θ * Real.exp (-(1 / (8 * θ)) * r ^ 2) ≤
            d / θ * Real.exp (-(1 / (16 * θ)) * r ^ 2) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
        exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right e1 hE0) e2)
          (by positivity)
    _ = (C₁ / θ ^ 2 + d / θ) * (2 * π * θ) ^ (-(d : ℝ) / 2) *
          Real.exp (-(1 / (16 * θ)) * r ^ 2) := by ring

variable {d : ℕ} {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsAddRightInvariant]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)]

/-! ### Kernel convolutions along `ι` -/

/-- **INF04 T4 `heatConvK`.** Convolution of `u : G → E` with a scalar kernel `K` on `ℝ^d`
along `ι`: `x ↦ ∫ K(y) u(x - ιy) dy` (the Bochner integral; it is the meaningful convolution
where `y ↦ K(y) u(x - ιy)` is integrable). For `K = G_θ` it is `heatConv ι θ`. -/
def heatConvK (ι : Euc d →+ G) (K : Euc d → ℝ) (u : G → E) (x : G) : E :=
  ∫ y : Euc d, K y • u (x - ι y)

theorem heatConvK_gaussKernel (ι : Euc d →+ G) (θ : ℝ) (u : G → E) :
    heatConvK ι (gaussKernel d θ) u = heatConv ι θ u := rfl

/-- **INF04 T4 `heatLpK`.** The `L^p` form of `heatConvK`: the `Lp E p μ`-valued Bochner
integral `∫ K(y) τ_{ιy}u dy` of translates (meaningful for integrable `K`, `p < ∞`). -/
def heatLpK (ι : Euc d →+ G) (hι : Continuous ι) (K : Euc d → ℝ) (u : Lp E p μ) : Lp E p μ :=
  ∫ y : Euc d, K y • translateLp ι hι y u

variable [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [R1Space G]

/-- For `θ > 0` and `p < ∞`, `heatLp ι hι θ = heatLpK ι hι G_θ` (`heatLp_eq_integral`). -/
theorem heatLp_eq_heatLpK (ι : Euc d →+ G) (hι : Continuous ι) (hp : p ≠ ∞) {θ : ℝ}
    (hθ : 0 < θ) (u : Lp E p μ) : heatLp ι hι θ u = heatLpK ι hι (gaussKernel d θ) u :=
  heatLp_eq_integral ι hι hp hθ u

/-- **INF04 T4 `hasDerivAt_heatLp_time`** (the generator, for BP5; B0447–B0450). For
`1 ≤ p < ∞`, `θ > 0` and `u ∈ L^p(G)`, the heat semigroup is differentiable in `θ` in the norm
of `L^p`, with `d/dθ e^{θΔ}u = ∫ ∂_θG_θ(y) τ_{ιy}u dy`. -/
theorem hasDerivAt_heatLp_time (ι : Euc d →+ G) (hι : Continuous ι) (hp : p ≠ ∞) {θ : ℝ}
    (hθ : 0 < θ) (u : Lp E p μ) :
    HasDerivAt (fun s => heatLp ι hι s u) (heatLpK ι hι (gaussDt d θ) u) θ := by
  obtain ⟨A, hA0, hA⟩ := abs_gaussDt_le (d := d) hθ
  set T : Euc d → Lp E p μ := fun y => translateLp ι hι y u with hT
  have hTc : Continuous T := continuous_translateLp ι hι hp u
  have hTn : ∀ y, ‖T y‖ = ‖u‖ := fun y => norm_translateLp ι hι y u
  have hball : Ioo (θ / 2) (2 * θ) ∈ 𝓝 θ := Ioo_mem_nhds (by linarith) (by linarith)
  have hbound : Integrable (fun y : Euc d => A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) * ‖u‖) :=
    ((Gaussian.integrable_exp_neg_mul_sq_norm (by positivity)).const_mul A).mul_const ‖u‖
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc d)))
    (F := fun s y => gaussKernel d s y • T y) (F' := fun s y => gaussDt d s y • T y)
    (bound := fun y => A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) * ‖u‖) hball
    (Eventually.of_forall fun s =>
      ((Gaussian.continuous_gaussKernel s).smul hTc).aestronglyMeasurable)
    (integrable_gauss_translateLp ι hι hp hθ u)
    ((continuous_gaussDt d θ).smul hTc).aestronglyMeasurable
    (Eventually.of_forall fun y s hs => by
      rw [norm_smul, hTn, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hA s hs.1 hs.2 y) (norm_nonneg _))
    hbound
    (Eventually.of_forall fun y s hs =>
      (hasDerivAt_gaussKernel_time (by linarith [hs.1]) y).smul_const (T y))
  refine hd.2.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hθ] with s hs
  exact heatLp_eq_integral ι hι hp hs u

end UnforcedLeray.Heat
