import UnforcedLeray.Lib.HeatR3.Generator
import UnforcedLeray.Lib.Gaussian.Absorb

/-!
# Directional derivatives of the generic heat convolution (INF04 T4, generic group)


item `hasDerivAt_heatConv_dir`, on a general group `G` with a homomorphism `ι : ℝ^d → G`
(decision D17; the cylinder `AddCircle c × ℝ` and the line are the cases of INF05: B0142,
B0296, B0224).

For bounded strongly measurable `u : G → E`, `θ > 0` and every `x ∈ G`, along the direction
`ι(e_i)`:

`d/dr|_{r=0} heatConv ι θ u (x + ι(r e_i)) = heatConvK ι (∂_iG_θ) u x`,
`∂_iG_θ(y) = -(y_i/(2θ)) G_θ(y)` (`gaussD1`).

Proof: the translation `y ↦ y + r e_i` of `ℝ^d` moves the shift onto the kernel,
`heatConv ι θ u (x + ι(re_i)) = ∫ G_θ(y + re_i) u(x - ιy) dy`, and the kernel is differentiated
under the integral (Gaussian envelope uniform in `|r| < 1`). The statement is pointwise (every
`x`); for `L^p` data the heat integral at a given `x` need not converge on a general group
(e.g. when `ι(ℝ^d)` is a null subgroup), which is why the data are bounded here; the `ℝ³`
`L^p` smoothing bound is `eLpNorm_fderiv_average_apply_le` (`Smoothing`).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology Real
open scoped ENNReal RealInnerProductSpace
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- **INF04 T2/T4 `gaussD1`.** `∂_iG_θ(y) = -(y_i/(2θ)) G_θ(y)`. -/
def gaussD1 (d : ℕ) (θ : ℝ) (i : Fin d) (y : Euc d) : ℝ :=
  -(y i) / (2 * θ) * gaussKernel d θ y

theorem continuous_gaussD1 (d : ℕ) (θ : ℝ) (i : Fin d) : Continuous (gaussD1 d θ i) := by
  unfold gaussD1
  exact (((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.neg).div_const _).mul
    (Gaussian.continuous_gaussKernel θ)

/-- `r ↦ G_θ(y + r e_i)` has derivative `∂_iG_θ(y + r e_i)`. -/
theorem hasDerivAt_gaussKernel_shift {d : ℕ} {θ : ℝ} (hθ : 0 < θ) (i : Fin d) (y : Euc d)
    (r : ℝ) :
    HasDerivAt (fun r : ℝ => gaussKernel d θ (y + r • EuclideanSpace.single i 1))
      (gaussD1 d θ i (y + r • EuclideanSpace.single i 1)) r := by
  set e : Euc d := EuclideanSpace.single i 1 with he
  have hz : HasDerivAt (fun r : ℝ => y + r • e) e r := by
    simpa using ((hasDerivAt_id r).smul_const e).const_add y
  have hn : HasDerivAt (fun r : ℝ => ‖y + r • e‖ ^ 2) (2 * ⟪y + r • e, e⟫) r := hz.norm_sq
  have hexp := (hn.fun_neg.div_const (4 * θ)).exp
  have h := hexp.const_mul ((4 * π * θ) ^ (-(d : ℝ) / 2))
  have hinner : ⟪y + r • e, e⟫ = (y + r • e) i := by
    rw [he, EuclideanSpace.inner_single_right]; simp
  refine h.congr_deriv ?_
  rw [hinner]
  unfold gaussD1 gaussKernel
  field_simp
  ring

/-- A Gaussian envelope for `∂_iG_θ(y + r e_i)`, uniform in `|r| < 1`. -/
theorem abs_gaussD1_shift_le {d : ℕ} {θ : ℝ} (hθ : 0 < θ) (i : Fin d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, |r| < 1 → ∀ y : Euc d,
      |gaussD1 d θ i (y + r • EuclideanSpace.single i 1)| ≤
        A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := Gaussian.rpow_mul_exp_neg_mul_sq_le (m := 1) (b := 1 / (8 * θ))
    (by norm_num) (by positivity)
  set c := (4 * π * θ) ^ (-(d : ℝ) / 2)
  have hc : 0 ≤ c := by positivity
  refine ⟨c / (2 * θ) * K * Real.exp (1 / (8 * θ)), by positivity, fun r hr y => ?_⟩
  set z := y + r • EuclideanSpace.single i (1 : ℝ) with hzdef
  have hzi : |z i| ≤ ‖z‖ := by
    rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le z i
  have hyz : ‖y‖ ≤ ‖z‖ + 1 := by
    have hre : ‖r • EuclideanSpace.single i (1 : ℝ)‖ = |r| := by
      rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have h1 := norm_sub_le (y + r • EuclideanSpace.single i (1 : ℝ))
      (r • EuclideanSpace.single i (1 : ℝ))
    rw [add_sub_cancel_right, hre, ← hzdef] at h1
    linarith
  have hsq : ‖y‖ ^ 2 / 2 - 1 ≤ ‖z‖ ^ 2 := by
    have h1 := mul_self_le_mul_self (norm_nonneg y) hyz
    nlinarith [sq_nonneg (‖z‖ - 1)]
  -- the three factors
  have hG : gaussKernel d θ z = c * Real.exp (-‖z‖ ^ 2 / (4 * θ)) := rfl
  have hsplit : Real.exp (-‖z‖ ^ 2 / (4 * θ)) =
      Real.exp (-(1 / (8 * θ) * ‖z‖ ^ 2)) * Real.exp (-‖z‖ ^ 2 / (8 * θ)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hpoly : ‖z‖ * Real.exp (-(1 / (8 * θ) * ‖z‖ ^ 2)) ≤ K := by
    have := hK ‖z‖ (norm_nonneg z); rwa [Real.rpow_one] at this
  have htail : Real.exp (-‖z‖ ^ 2 / (8 * θ)) ≤
      Real.exp (1 / (8 * θ)) * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h8 : 0 < 8 * θ := by positivity
    rw [neg_div, div_eq_mul_inv, show 1 / (16 * θ) = (1 / 2) * (8 * θ)⁻¹ by field_simp; ring,
      one_div]
    nlinarith [inv_pos.mpr h8]
  unfold gaussD1
  rw [hG, abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * θ),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * Real.exp (-‖z‖ ^ 2 / (4 * θ))), hsplit]
  calc |z i| / (2 * θ) * (c * (Real.exp (-(1 / (8 * θ) * ‖z‖ ^ 2)) *
        Real.exp (-‖z‖ ^ 2 / (8 * θ))))
      ≤ ‖z‖ / (2 * θ) * (c * (Real.exp (-(1 / (8 * θ) * ‖z‖ ^ 2)) *
        Real.exp (-‖z‖ ^ 2 / (8 * θ)))) := by gcongr
    _ = c / (2 * θ) * (‖z‖ * Real.exp (-(1 / (8 * θ) * ‖z‖ ^ 2))) *
        Real.exp (-‖z‖ ^ 2 / (8 * θ)) := by ring
    _ ≤ c / (2 * θ) * K * (Real.exp (1 / (8 * θ)) * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2)) := by
        gcongr
    _ = c / (2 * θ) * K * Real.exp (1 / (8 * θ)) * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) := by
        ring

variable {d : ℕ} {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **INF04 T4 `hasDerivAt_heatConv_dir`** (generic group; B0142, B0296, B0224). For `θ > 0`,
bounded strongly measurable `u : G → E`, every `x ∈ G` and every coordinate direction `e_i`:
`r ↦ heatConv ι θ u (x + ι(r e_i))` is differentiable at `0` with derivative
`heatConvK ι (∂_iG_θ) u x = ∫ ∂_iG_θ(y) u(x - ιy) dy`. -/
theorem hasDerivAt_heatConv_dir (ι : Euc d →+ G) (hι : Measurable ι) {θ : ℝ} (hθ : 0 < θ)
    {u : G → E} (hu : StronglyMeasurable u) {M : ℝ} (hM : ∀ x, ‖u x‖ ≤ M) (i : Fin d)
    (x : G) :
    HasDerivAt (fun r : ℝ => heatConv ι θ u (x + ι (r • EuclideanSpace.single i 1)))
      (heatConvK ι (gaussD1 d θ i) u x) 0 := by
  set e : Euc d := EuclideanSpace.single i 1 with he
  obtain ⟨A, hA0, hA⟩ := abs_gaussD1_shift_le (d := d) hθ i
  have hus : StronglyMeasurable fun y : Euc d => u (x - ι y) :=
    hu.comp_measurable (measurable_const.sub hι)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
  -- the shift moves onto the kernel
  have hrep : ∀ r : ℝ, heatConv ι θ u (x + ι (r • e)) =
      ∫ y : Euc d, gaussKernel d θ (y + r • e) • u (x - ι y) := by
    intro r
    unfold heatConv
    rw [← integral_add_right_eq_self (fun y : Euc d => gaussKernel d θ y • u (x + ι (r • e) - ι y))
      (r • e)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [map_add]
    congr 2
    abel
  have hball : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hbound : Integrable (fun y : Euc d => A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) * M) :=
    ((Gaussian.integrable_exp_neg_mul_sq_norm (by positivity)).const_mul A).mul_const M
  have hcont : ∀ r : ℝ, Continuous fun y : Euc d => gaussKernel d θ (y + r • e) :=
    fun r => (Gaussian.continuous_gaussKernel θ).comp (continuous_id.add continuous_const)
  have hint0 : Integrable (fun y : Euc d => gaussKernel d θ (y + (0 : ℝ) • e) • u (x - ι y)) := by
    refine ((Gaussian.integrable_gaussKernel hθ).mul_const M).mono'
      ((hcont 0).aestronglyMeasurable.smul hus.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [zero_smul, add_zero, norm_smul, Real.norm_of_nonneg (Gaussian.gaussKernel_nonneg hθ y)]
    exact mul_le_mul_of_nonneg_left (hM _) (Gaussian.gaussKernel_nonneg hθ y)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc d)))
    (F := fun r y => gaussKernel d θ (y + r • e) • u (x - ι y))
    (F' := fun r y => gaussD1 d θ i (y + r • e) • u (x - ι y))
    (bound := fun y => A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) * M) hball
    (Eventually.of_forall fun r =>
      (hcont r).aestronglyMeasurable.smul hus.aestronglyMeasurable)
    hint0
    (((continuous_gaussD1 d θ i).comp (continuous_id.add continuous_const)).aestronglyMeasurable.smul
      hus.aestronglyMeasurable)
    (Eventually.of_forall fun y r hr => by
      rw [norm_smul, Real.norm_eq_abs]
      have hr' : |r| < 1 := abs_lt.mpr ⟨hr.1, hr.2⟩
      exact mul_le_mul (hA r hr' y) (hM _) (norm_nonneg _) (by positivity))
    hbound
    (Eventually.of_forall fun y r _ =>
      (hasDerivAt_gaussKernel_shift hθ i y r).smul_const (u (x - ι y)))
  have h2 := hd.2
  simp only [zero_smul, add_zero] at h2
  exact h2.congr_of_eventuallyEq (Eventually.of_forall hrep)

end UnforcedLeray.Heat
