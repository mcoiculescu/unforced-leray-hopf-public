import UnforcedLeray.Lib.HeatR3.Space
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Order.CompletePartialOrder

/-!
# Heat flow of bounded data and of `C^k_b` data on `ℝ³` (INF04 T7, part)


Covers the heat steps of units B0720, B0722 (bounded and `W^{k,∞}` data, tex 5260–5330), and the
commutation of the heat flow with the divergence used in B0672.

Main results:
* `norm_heatConv_le_of_bound` (generic group) and `norm_average_le_of_bound`:
  `|e^{θΔ}u(x)| ≤ sup |u|` at every point, `θ > 0`, with no measurability hypothesis;
* `hasFDerivAt_average`, `fderiv_average`: for `u ∈ C¹` with `u, Du` bounded,
  `D(e^{θΔ}u) = e^{θΔ}(Du)` (dominated differentiation);
* `iteratedFDeriv_average`: for `u ∈ C^n` with `D^k u` bounded for `k ≤ n`,
  `D^k(e^{θΔ}u) = e^{θΔ}(D^k u)` for `k ≤ n` (the scoping note asks for `n = 2`);
* `norm_iteratedFDeriv_average_le`: `|D^k e^{θΔ}u| ≤ sup |D^k u|`;
* `spaceDiv`, `spaceDiv_average`: `div(e^{θΔ}u) = e^{θΔ}(div u)` for `u ∈ C¹_b`.

Not proved here (see the status report): the heat FTC
`e^{θΔ}u - u = ∫_0^θ e^{tΔ}Δu dt` for `C²_b` data.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Gaussian (Euc gaussKernel)

section Generic

variable {d : ℕ} {G : Type*} [AddCommGroup G] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- **INF04 T7, generic form.** If `‖u x‖ ≤ M` for every `x`, then `‖e^{θΔ}u(x)‖ ≤ M` for every
`x` and `θ > 0`. No measurability hypothesis is needed: a divergent integral is `0 ≤ M`. -/
theorem norm_heatConv_le_of_bound (ι : Euc d →+ G) {θ : ℝ} (hθ : 0 < θ) {u : G → E} {M : ℝ}
    (hu : ∀ x, ‖u x‖ ≤ M) (x : G) : ‖heatConv ι θ u x‖ ≤ M := by
  have hint : Integrable (fun y : Euc d => gaussKernel d θ y * M) :=
    (Gaussian.integrable_gaussKernel hθ).mul_const M
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_smul, Real.norm_of_nonneg (Gaussian.gaussKernel_nonneg hθ y)]
    exact mul_le_mul_of_nonneg_left (hu _) (Gaussian.gaussKernel_nonneg hθ y)
  · rw [integral_mul_const, Gaussian.integral_gaussKernel hθ, one_mul]

end Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem continuous_kernel (θ : ℝ) : Continuous (kernel θ) := by
  rw [← Gaussian.gaussKernel_three_eq]; exact Gaussian.continuous_gaussKernel θ

/-- **INF04 T7 `norm_average_le_of_bound`.** `‖e^{θΔ}u(x)‖ ≤ M` when `‖u‖ ≤ M` everywhere
(tex 5260–5330, B0720). -/
theorem norm_average_le_of_bound {θ : ℝ} (hθ : 0 < θ) {u : Space → E} {M : ℝ}
    (hu : ∀ x, ‖u x‖ ≤ M) (x : Space) : ‖average θ u x‖ ≤ M := by
  rw [← heatConv_space_eq_average]
  exact norm_heatConv_le_of_bound _ hθ hu x

/-- The heat integrand of a continuous bounded field is integrable. -/
theorem integrable_average_of_bound {θ : ℝ} (hθ : 0 < θ) {u : Space → E} (hc : Continuous u)
    {M : ℝ} (hu : ∀ x, ‖u x‖ ≤ M) (x : Space) :
    Integrable (fun y : Space => kernel θ y • u (x - y)) := by
  have hm : Continuous (fun y : Space => kernel θ y • u (x - y)) :=
    (continuous_kernel θ).smul (hc.comp (continuous_const.sub continuous_id))
  refine ((kernel_integrable hθ).mul_const M).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  · rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg hθ y)]
    exact mul_le_mul_of_nonneg_left (hu _) (kernel_nonneg hθ y)

/-- **INF04 T7, first derivative.** For `u ∈ C¹(ℝ³)` with `‖u‖ ≤ M` and `‖Du‖ ≤ M`,
`e^{θΔ}u` is differentiable with `D(e^{θΔ}u)(x) = e^{θΔ}(Du)(x)` (dominated differentiation
under the Gaussian integral). -/
theorem hasFDerivAt_average {θ : ℝ} (hθ : 0 < θ) {u : Space → E} (hu : ContDiff ℝ 1 u)
    {M : ℝ} (hb0 : ∀ x, ‖u x‖ ≤ M) (hb1 : ∀ x, ‖fderiv ℝ u x‖ ≤ M) (x : Space) :
    HasFDerivAt (average θ u) (average θ (fderiv ℝ u) x) x := by
  have hc : Continuous u := hu.continuous
  have hc' : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ u := hu.differentiable one_ne_zero
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := (volume : Measure Space))
    (F := fun x' y => kernel θ y • u (x' - y))
    (F' := fun x' y => kernel θ y • fderiv ℝ u (x' - y))
    (bound := fun y => kernel θ y * M) (x₀ := x) (s := univ) univ_mem
    (Eventually.of_forall fun x' => (integrable_average_of_bound hθ hc hb0 x').1)
    (integrable_average_of_bound hθ hc hb0 x)
    (integrable_average_of_bound hθ hc' hb1 x).1
    (Eventually.of_forall fun y x' _ => by
      rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg hθ y)]
      exact mul_le_mul_of_nonneg_left (hb1 _) (kernel_nonneg hθ y))
    ((kernel_integrable hθ).mul_const M)
    (Eventually.of_forall fun y x' _ => by
      have h1 : HasFDerivAt (fun z : Space => z - y) (ContinuousLinearMap.id ℝ Space) x' :=
        (hasFDerivAt_id x').sub_const y
      have h3 : HasFDerivAt (fun z : Space => u (z - y)) (fderiv ℝ u (x' - y)) x' := by
        have h := (hdiff (x' - y)).hasFDerivAt.comp x' h1
        rwa [ContinuousLinearMap.comp_id] at h
      exact h3.const_smul (kernel θ y))
  exact key

theorem fderiv_average {θ : ℝ} (hθ : 0 < θ) {u : Space → E} (hu : ContDiff ℝ 1 u)
    {M : ℝ} (hb0 : ∀ x, ‖u x‖ ≤ M) (hb1 : ∀ x, ‖fderiv ℝ u x‖ ≤ M) :
    fderiv ℝ (average θ u) = average θ (fderiv ℝ u) :=
  funext fun x => (hasFDerivAt_average hθ hu hb0 hb1 x).fderiv

/-- A linear isometric equivalence passes through the heat integral. -/
theorem average_linearIsometryEquiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (L : E ≃ₗᵢ[ℝ] F) (θ : ℝ) (u : Space → E) (x : Space) :
    average θ (fun y => L (u y)) x = L (average θ u x) := by
  simp only [average]
  have h := (L.toLinearIsometry).integral_comp_comm
    (μ := (volume : Measure Space)) (fun y => kernel θ y • u (x - y))
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.map_smul] using h

/-- **INF04 T7 `iteratedFDeriv_average`.** For `u ∈ C^n(ℝ³)` with `‖D^k u‖ ≤ M` for every
`k ≤ n`, `D^k(e^{θΔ}u) = e^{θΔ}(D^k u)` for every `k ≤ n` (`θ > 0`). The scoping note's
statement is the case `n = 2`. -/
theorem iteratedFDeriv_average {θ : ℝ} (hθ : 0 < θ) {n : ℕ} {u : Space → E}
    (hu : ContDiff ℝ n u) {M : ℝ} (hb : ∀ k ≤ n, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ M) :
    ∀ k ≤ n, iteratedFDeriv ℝ k (average θ u) = average θ (iteratedFDeriv ℝ k u) := by
  intro k
  induction k with
  | zero =>
    intro _
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    exact (average_linearIsometryEquiv
      (continuousMultilinearCurryFin0 ℝ Space E).symm θ u x).symm
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have hv : ContDiff ℝ 1 (iteratedFDeriv ℝ k u) :=
      hu.iteratedFDeriv_right (by rw [add_comm]; exact_mod_cast hk)
    have hb1 : ∀ x, ‖fderiv ℝ (iteratedFDeriv ℝ k u) x‖ ≤ M := fun x => by
      rw [norm_fderiv_iteratedFDeriv]; exact hb (k + 1) hk x
    rw [iteratedFDeriv_succ_eq_comp_left, ih hk', fderiv_average hθ hv (hb k hk') hb1,
      iteratedFDeriv_succ_eq_comp_left]
    funext x
    simp only [Function.comp_apply]
    exact (average_linearIsometryEquiv
      (E := Space →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) E)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => Space) E)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space) E).symm θ _ x).symm

/-- **INF04 T7.** `‖D^k e^{θΔ}u(x)‖ ≤ M` for `u ∈ C^n`, `‖D^j u‖ ≤ M` (`j ≤ n`), `k ≤ n`. -/
theorem norm_iteratedFDeriv_average_le {θ : ℝ} (hθ : 0 < θ) {n : ℕ} {u : Space → E}
    (hu : ContDiff ℝ n u) {M : ℝ} (hb : ∀ k ≤ n, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ M)
    {k : ℕ} (hk : k ≤ n) (x : Space) :
    ‖iteratedFDeriv ℝ k (average θ u) x‖ ≤ M := by
  rw [iteratedFDeriv_average hθ hu hb k hk]
  exact norm_average_le_of_bound hθ (hb k hk) x

/-- The divergence `div u = Σ_i ∂_i u_i` of a vector field on `ℝ³` (coordinate form of the
compiled `spatialDivergence`, `lean/UnforcedLeray/Statement.lean`). -/
def spaceDiv (u : SpatialField) (x : Space) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ u x (coordinateVector i)) i

/-- **INF04 T7 `divergence_average`.** `div(e^{θΔ}u) = e^{θΔ}(div u)` for `u ∈ C¹_b(ℝ³; ℝ³)`
(B0672: the heat flow preserves solenoidality). -/
theorem spaceDiv_average {θ : ℝ} (hθ : 0 < θ) {u : SpatialField} (hu : ContDiff ℝ 1 u)
    {M : ℝ} (hb0 : ∀ x, ‖u x‖ ≤ M) (hb1 : ∀ x, ‖fderiv ℝ u x‖ ≤ M) (x : Space) :
    spaceDiv (average θ u) x = average θ (spaceDiv u) x := by
  have hc' : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  simp only [spaceDiv]
  rw [fderiv_average hθ hu hb0 hb1]
  have hint := integrable_average_of_bound hθ hc' hb1 x
  have hcomp : ∀ i : Fin 3, (average θ (fderiv ℝ u) x (coordinateVector i)) i =
      average θ (fun y => (fderiv ℝ u y (coordinateVector i)) i) x := by
    intro i
    let L : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
      (EuclideanSpace.proj i).comp (ContinuousLinearMap.apply ℝ Space (coordinateVector i))
    have h := L.integral_comp_comm hint
    simp only [average]
    simpa [L] using h.symm
  simp_rw [hcomp]
  simp only [average]
  rw [← integral_finset_sum]
  · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [spaceDiv, Finset.smul_sum]
  · intro i _
    let L : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
      (EuclideanSpace.proj i).comp (ContinuousLinearMap.apply ℝ Space (coordinateVector i))
    have h := L.integrable_comp hint
    simpa [L] using h

end UnforcedLeray.Heat
