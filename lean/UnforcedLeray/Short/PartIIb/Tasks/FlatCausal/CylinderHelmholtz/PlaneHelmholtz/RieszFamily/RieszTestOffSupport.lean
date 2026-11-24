import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvGradKernel
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvContDiff
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneRieszKernelEq
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneRieszKernelBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PlaneRieszKernelMeasurable

/-!
# Leaf `PartII-b:T12/1/1/2/21`: kernel representation of the planar Riesz pair off the support

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula);
classical Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `f` and `x ∉ tsupport f`,
`∂_i ∂_k (N * f)(x) = ∫ K_{ik}(x - y) f(y) dy`.  The proof differentiates the kernel integral
for `∂_k (N * f)` (`NewtonConvGradKernel`) under the integral sign along the line `x + t e_i`,
`|t| < δ`, where the integrand stays at distance `≥ δ` from its singularity
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`); the derivative of `∂_k N` is the Riesz
kernel off the origin (`PlaneRieszKernelEq`) and is bounded by `(δ²)⁻¹` (`PlaneRieszKernelBound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The gradient kernel satisfies `|∂_kN(z)| ≤ (2π)⁻¹ ‖z‖⁻¹` for every `z`. -/
theorem abs_newtonGradKernel_le_inv' (k : Fin 2) (z : Pl) :
    |newtonGradKernel k z| ≤ (2 * Real.pi)⁻¹ * ‖z‖⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    simp [newtonGradKernel]
  · have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hc : ∀ j : Fin 2, z j ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by
      have hc0 : z 0 ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by linarith [sq_nonneg (z 1)]
      have hc1 : z 1 ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by linarith [sq_nonneg (z 0)]
      intro j
      fin_cases j
      · exact hc0
      · exact hc1
    have hs0 : 0 ≤ z 0 ^ 2 + z 1 ^ 2 := by positivity
    have hnorm_le : ‖z‖ ≤ Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr ?_
      intro j
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (hc j)
    have hsq : ‖z‖ ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg z) hnorm_le 2
      rwa [Real.sq_sqrt hs0] at h
    have hs : 0 < z 0 ^ 2 + z 1 ^ 2 := lt_of_lt_of_le (pow_pos hnz 2) hsq
    have hfac : 0 < (2 * Real.pi)⁻¹ := by positivity
    have hk : |z k| ≤ ‖z‖ := by
      have := norm_le_pi_norm z k
      rwa [Real.norm_eq_abs] at this
    have hmain : |z k| / (z 0 ^ 2 + z 1 ^ 2) ≤ ‖z‖⁻¹ := by
      rw [div_le_iff₀ hs]
      calc |z k| ≤ ‖z‖ := hk
        _ = ‖z‖⁻¹ * ‖z‖ ^ 2 := by
          rw [sq, ← mul_assoc, inv_mul_cancel₀ hnz.ne', one_mul]
        _ ≤ ‖z‖⁻¹ * (z 0 ^ 2 + z 1 ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hnz.le)
    unfold newtonGradKernel
    rw [abs_div, abs_mul, abs_of_pos hfac, abs_of_pos hs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hmain hfac.le

/-- A point outside the closed support has positive distance to the support. -/
theorem exists_pos_two_mul_le_norm_sub {f : Pl → ℝ} {x : Pl} (hx : x ∉ tsupport f) :
    ∃ δ > 0, ∀ y, f y ≠ 0 → 2 * δ ≤ ‖x - y‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isClosed_tsupport f).isOpen_compl x hx
  refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
  have hyt : y ∈ tsupport f := subset_tsupport f hy
  have hy' : y ∉ ball x ε := fun h => hball h hyt
  rw [mem_ball, not_lt, dist_eq_norm] at hy'
  rw [norm_sub_rev]
  linarith

/-- The gradient kernel is differentiable away from the origin. -/
theorem differentiableAt_newtonGradKernel_of_ne (k : Fin 2) {z : Pl} (hz : z ≠ 0) :
    DifferentiableAt ℝ (newtonGradKernel k) z := by
  have hD : z 0 ^ 2 + z 1 ^ 2 ≠ 0 := by
    intro h
    apply hz
    have h0' : z 0 ^ 2 = 0 :=
      le_antisymm (by linarith [sq_nonneg (z 1), sq_nonneg (z 0)]) (sq_nonneg _)
    have h1' : z 1 ^ 2 = 0 :=
      le_antisymm (by linarith [sq_nonneg (z 1), sq_nonneg (z 0)]) (sq_nonneg _)
    have h0 : z 0 = 0 := (pow_eq_zero_iff two_ne_zero).mp h0'
    have h1 : z 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h1'
    funext j
    fin_cases j
    · simpa using h0
    · simpa using h1
  unfold newtonGradKernel
  fun_prop (disch := exact hD)

/-- The gradient kernel is measurable. -/
theorem measurable_newtonGradKernel' (k : Fin 2) : Measurable (newtonGradKernel k) := by
  unfold newtonGradKernel
  fun_prop

/-- Points at distance `≥ δ` from the support stay at distance `≥ δ` along the line `x + t e_i`,
`|t| < δ`. -/
theorem near_line (i : Fin 2) {f : Pl → ℝ} {x : Pl} {δ : ℝ} (hsep : ∀ y, f y ≠ 0 → 2 * δ ≤ ‖x - y‖)
    (y : Pl) (hy : f y ≠ 0) (t : ℝ) (ht : t ∈ ball (0 : ℝ) δ) :
    δ ≤ ‖x + t • Pi.single i (1 : ℝ) - y‖ := by
  have h2 := hsep y hy
  have ht' : |t| < δ := by simpa [Real.norm_eq_abs] using ht
  have hte : ‖t • Pi.single i (1 : ℝ)‖ = |t| := by
    rw [norm_smul, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  have h3 : ‖x - y‖ - ‖t • Pi.single i (1 : ℝ)‖ ≤ ‖x + t • Pi.single i (1 : ℝ) - y‖ := by
    have := norm_sub_norm_le (x - y) (-(t • Pi.single i (1 : ℝ)))
    rw [norm_neg, sub_neg_eq_add] at this
    calc ‖x - y‖ - ‖t • Pi.single i (1 : ℝ)‖ ≤ ‖x - y + t • Pi.single i (1 : ℝ)‖ := this
      _ = ‖x + t • Pi.single i (1 : ℝ) - y‖ := by congr 1; abel
  linarith

/-- The derivative of `s ↦ ∂_kN(x + s e_i - y)` at a point off the singularity is the
planar Riesz kernel. -/
theorem hasDerivAt_gradKernelLine_off (i k : Fin 2) (x y : Pl) (t : ℝ)
    (hz : x + t • Pi.single i (1 : ℝ) - y ≠ 0) :
    HasDerivAt (fun s : ℝ => newtonGradKernel k (x + s • Pi.single i (1 : ℝ) - y))
      (planeRieszKernel i k (x + t • Pi.single i (1 : ℝ) - y)) t := by
  have hG' : HasFDerivAt (newtonGradKernel k)
      (fderiv ℝ (newtonGradKernel k) (x + t • Pi.single i (1 : ℝ) - y))
      (x + t • Pi.single i (1 : ℝ) - y) :=
    (differentiableAt_newtonGradKernel_of_ne k hz).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => x + s • Pi.single i (1 : ℝ) - y)
      (Pi.single i (1 : ℝ)) t := by
    have h := (((hasDerivAt_id t).smul_const (Pi.single i (1 : ℝ))).const_add x).sub_const y
    simpa using h
  have h := hG'.comp_hasDerivAt t hline
  rw [planeRieszKernelEq i k _ hz] at h
  exact h

/-- The derivative of `∂_k (N * f)` along the line `x + t e_i` at `t = 0`. -/
theorem hasDerivAt_pd_line (i k : Fin 2) {f : Pl → ℝ} (hf : IsTest f) (x : Pl) :
    HasDerivAt (fun t : ℝ => pd k (newtonConv f) (x + t • Pi.single i (1 : ℝ)))
      (fderiv ℝ (pd k (newtonConv f)) x (Pi.single i 1)) 0 := by
  have hU : ContDiff ℝ ∞ (newtonConv f) := newtonConvContDiff f hf
  have hG : ContDiff ℝ ∞ (pd k (newtonConv f)) := by
    unfold pd
    exact (hU.fderiv_right (by simp)).clm_apply contDiff_const
  have hl : HasDerivAt (fun s : ℝ => x + s • Pi.single i (1 : ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add x
  have hd : HasFDerivAt (pd k (newtonConv f)) (fderiv ℝ (pd k (newtonConv f)) x)
      (x + (0 : ℝ) • Pi.single i (1 : ℝ)) := by
    rw [zero_smul, add_zero]
    exact (hG.differentiable (by simp) x).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℝ) hl

/-- The gradient-kernel integrand along the line `x + t e_i`. -/
def lineGrad (i k : Fin 2) (f : Pl → ℝ) (x : Pl) (t : ℝ) (y : Pl) : ℝ :=
  newtonGradKernel k (x + t • Pi.single i (1 : ℝ) - y) * f y

/-- The planar Riesz-kernel integrand along the line `x + t e_i`. -/
def lineRiesz (i k : Fin 2) (f : Pl → ℝ) (x : Pl) (t : ℝ) (y : Pl) : ℝ :=
  planeRieszKernel i k (x + t • Pi.single i (1 : ℝ) - y) * f y

/-- Measurability of the gradient-kernel integrand along the line. -/
theorem measurable_lineGrad (i k : Fin 2) {f : Pl → ℝ} (hf : IsTest f) (x : Pl) (t : ℝ) :
    AEStronglyMeasurable (lineGrad i k f x t) volume :=
  (((measurable_newtonGradKernel' k).comp
      (continuous_const.sub continuous_id).measurable).mul
        hf.1.continuous.measurable).aestronglyMeasurable

/-- Measurability of the Riesz integrand along the line. -/
theorem measurable_lineRiesz (i k : Fin 2) {f : Pl → ℝ} (hf : IsTest f) (x : Pl) (t : ℝ) :
    AEStronglyMeasurable (lineRiesz i k f x t) volume :=
  (((planeRieszKernelMeasurable i k).comp
      (continuous_const.sub continuous_id).measurable).mul
        hf.1.continuous.measurable).aestronglyMeasurable

/-- Integrability of the gradient-kernel integrand at `t = 0`. -/
theorem integrable_lineGrad_zero (i k : Fin 2) {f : Pl → ℝ} (hf : IsTest f) {x : Pl}
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ y, f y ≠ 0 → 2 * δ ≤ ‖x - y‖) :
    Integrable (lineGrad i k f x 0) volume := by
  have hfi : Integrable f volume := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  refine (hfi.abs.const_mul ((2 * Real.pi)⁻¹ * δ⁻¹)).mono'
    (measurable_lineGrad i k hf x 0) (Eventually.of_forall fun y => ?_)
  by_cases hy : f y = 0
  · simp [lineGrad, hy]
  · have hz : δ ≤ ‖x + (0 : ℝ) • Pi.single i (1 : ℝ) - y‖ :=
      near_line i hsep y hy 0 (mem_ball_self hδ)
    have hgb : |newtonGradKernel k (x + (0 : ℝ) • Pi.single i (1 : ℝ) - y)| ≤
        (2 * Real.pi)⁻¹ * δ⁻¹ :=
      (abs_newtonGradKernel_le_inv' k _).trans
        (mul_le_mul_of_nonneg_left (inv_anti₀ hδ hz) (by positivity))
    show ‖newtonGradKernel k (x + (0 : ℝ) • Pi.single i (1 : ℝ) - y) * f y‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hgb (abs_nonneg _)

/-- Pointwise bound of the Riesz integrand along the line. -/
theorem bound_lineRiesz (i k : Fin 2) {f : Pl → ℝ} {x : Pl} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ y, f y ≠ 0 → 2 * δ ≤ ‖x - y‖) :
    ∀ᵐ y ∂volume, ∀ t ∈ ball (0 : ℝ) δ, ‖lineRiesz i k f x t y‖ ≤ (δ ^ 2)⁻¹ * |f y| :=
  Eventually.of_forall fun y t ht => by
    by_cases hy : f y = 0
    · simp [lineRiesz, hy]
    · show ‖planeRieszKernel i k (x + t • Pi.single i (1 : ℝ) - y) * f y‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (planeRieszKernelBound i k δ _ hδ (near_line i hsep y hy t ht)) (abs_nonneg _)

/-- Pointwise derivative of the gradient-kernel integrand along the line. -/
theorem hasDerivAt_lineGrad_ae (i k : Fin 2) {f : Pl → ℝ} {x : Pl} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ y, f y ≠ 0 → 2 * δ ≤ ‖x - y‖) :
    ∀ᵐ y ∂volume, ∀ t ∈ ball (0 : ℝ) δ,
      HasDerivAt (fun s : ℝ => lineGrad i k f x s y) (lineRiesz i k f x t y) t :=
  Eventually.of_forall fun y t ht => by
    show HasDerivAt
      (fun s : ℝ => newtonGradKernel k (x + s • Pi.single i (1 : ℝ) - y) * f y)
      (planeRieszKernel i k (x + t • Pi.single i (1 : ℝ) - y) * f y) t
    by_cases hy : f y = 0
    · simp only [hy, mul_zero]
      exact hasDerivAt_const t (0 : ℝ)
    · have hz : x + t • Pi.single i (1 : ℝ) - y ≠ 0 := by
        intro h0
        have := near_line i hsep y hy t ht
        rw [h0, norm_zero] at this
        linarith
      exact (hasDerivAt_gradKernelLine_off i k x y t hz).mul_const (f y)

set_option maxHeartbeats 1000000 in
/-- Differentiation of the kernel integral along the line `x + t e_i` at `t = 0`. -/
theorem hasDerivAt_kernelIntegral (i k : Fin 2) {f : Pl → ℝ} (hf : IsTest f) {x : Pl}
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ y, f y ≠ 0 → 2 * δ ≤ ‖x - y‖) :
    HasDerivAt (fun t : ℝ => ∫ y, lineGrad i k f x t y)
      (∫ y, lineRiesz i k f x 0 y) 0 := by
  have hs : ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := ball_mem_nhds (0 : ℝ) hδ
  have hM : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (lineGrad i k f x t) volume :=
    Eventually.of_forall fun t => measurable_lineGrad i k hf x t
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := lineGrad i k f x) (F' := lineRiesz i k f x)
    hs hM (integrable_lineGrad_zero i k hf hδ hsep)
    (measurable_lineRiesz i k hf x 0)
    (bound_lineRiesz i k hδ hsep)
    ((Integrable.abs (hf.1.continuous.integrable_of_hasCompactSupport hf.2)).const_mul ((δ ^ 2)⁻¹))
    (hasDerivAt_lineGrad_ae i k hδ hsep)
  exact key.2

/-- **Leaf `PartII-b:T12/1/1/2/21`.**  Off the support of a planar test `f`,
`S_{ik} f(x) = ∫ K_{ik}(x - y) f(y) dy`. -/
theorem rieszTestOffSupport : RieszTestOffSupport := by
  intro i k f hf x hx
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_two_mul_le_norm_sub hx
  have hfun : (fun t : ℝ => ∫ y, lineGrad i k f x t y) =
      fun t : ℝ => pd k (newtonConv f) (x + t • Pi.single i (1 : ℝ)) := by
    funext t
    exact (newtonConvGradKernel k f hf _).symm
  have h2 := hasDerivAt_kernelIntegral i k hf hδ hsep
  rw [hfun] at h2
  have hu := (hasDerivAt_pd_line i k hf x).unique h2
  show fderiv ℝ (pd k (newtonConv f)) x (Pi.single i 1) = _
  rw [hu]
  unfold lineRiesz
  simp only [zero_smul, add_zero]

end UnforcedLeray.Short.IIb.PlaneRiesz
