import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3
import UnforcedLeray.Short.PartIIIa.T14_HeatGBound
import UnforcedLeray.Short.PartIIIa.SeparatedKernels
import UnforcedLeray.Analysis.Heat.KernelSemigroup

/-!
# `kf3HeatGConvFDeriv : KF3HeatGConvFDeriv` (source 3613-3616, heat semigroup)

`G_θ * ∂_jG_b = ∂_jG_{θ+b}`.  Route: the semigroup law `∫ G_θ(y) G_b(z - y) dy = G_{θ+b}(z)`
(`UnforcedLeray.Heat.integral_kernel_product`), differentiated in `z` under the integral
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`, bound `C b^{-2} ‖G_θ(y)‖`), then the
substitution `y ↦ x - y` (`integral_sub_left_eq_self`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.IIIa

theorem kf3hc_heatG_eq_kernel (a : ℝ) : heatG a = UnforcedLeray.Heat.kernel a :=
  heatG_eq_heatKernel

theorem kf3hc_smooth (a : ℝ) : ContDiff ℝ ∞ (heatG a) := by
  rw [heatG_eq_heatKernel]
  exact UnforcedLeray.Kernels.heatKernel_smooth a

theorem kf3hc_integrable {t : ℝ} (ht : 0 < t) : Integrable (heatG t) := by
  rw [heatG_eq_heatKernel]
  exact UnforcedLeray.Heat.kernel_integrable ht

/-- Uniform bound on the spatial derivative of `G_a` for `a > 0`. -/
theorem kf3hc_fderiv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), 0 < a → ∀ z : Space,
    ‖fderiv ℝ (heatG a) z‖ ≤ C * a ^ (-(2:ℝ)) := by
  obtain ⟨C1, hC1, hC1b⟩ := heatGBound 1
  refine ⟨C1, hC1, fun a ha z => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ 1 (heatG a) z‖ = ‖fderiv ℝ (heatG a) z‖ :=
    norm_iteratedFDeriv_one (heatG a)
  rw [← h1]
  have h := hC1b a ha z
  have e : -(3 + ((1:ℕ):ℝ)) / 2 = -(2:ℝ) := by norm_num
  rw [e] at h
  have hexp : Real.exp (-‖z‖ ^ 2 / (8 * a)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
    positivity
  have hpos : 0 ≤ C1 * a ^ (-(2:ℝ)) := mul_nonneg hC1 (Real.rpow_nonneg ha.le _)
  calc ‖iteratedFDeriv ℝ 1 (heatG a) z‖
      ≤ C1 * a ^ (-(2:ℝ)) * Real.exp (-‖z‖ ^ 2 / (8 * a)) := h
    _ ≤ C1 * a ^ (-(2:ℝ)) * 1 := mul_le_mul_of_nonneg_left hexp hpos
    _ = C1 * a ^ (-(2:ℝ)) := mul_one _

/-- **Leaf: the heat semigroup on a derivative** (source 3613-3616). -/
theorem kf3HeatGConvFDeriv : KF3HeatGConvFDeriv := by
  intro θ b hθ hb x j
  obtain ⟨C, hC, hCb⟩ := kf3hc_fderiv_bound
  -- the semigroup law, at every point
  have stepA : ∀ z : Space, ∫ y : Space, heatG θ y * heatG b (z - y) = heatG (θ + b) z := by
    intro z
    simp only [kf3hc_heatG_eq_kernel]
    exact UnforcedLeray.Heat.integral_kernel_product hθ hb z
  have hfun : (fun z : Space => ∫ y : Space, heatG θ y * heatG b (z - y)) = heatG (θ + b) :=
    funext stepA
  have hF_int : ∀ z : Space, Integrable (fun y : Space => heatG θ y * heatG b (z - y)) := by
    intro z
    have h := UnforcedLeray.Heat.kernel_product_integrable hθ hb z
    simpa only [kf3hc_heatG_eq_kernel] using h
  have hcont_fd : ∀ z : Space,
      Continuous (fun y : Space => heatG θ y • fderiv ℝ (heatG b) (z - y)) := by
    intro z
    refine (kf3hc_smooth θ).continuous.smul ?_
    exact ((kf3hc_smooth b).continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)
  have hdiffb : ∀ w : Space, HasFDerivAt (heatG b) (fderiv ℝ (heatG b) w) w := fun w =>
    ((kf3hc_smooth b).differentiable (by simp) w).hasFDerivAt
  have hcomp : ∀ z y : Space,
      HasFDerivAt (fun z' : Space => heatG b (z' - y)) (fderiv ℝ (heatG b) (z - y)) z := by
    intro z y
    have h1 : HasFDerivAt (fun z' : Space => z' - y) (ContinuousLinearMap.id ℝ Space) z :=
      (hasFDerivAt_id z).sub_const y
    have h2 := (hdiffb (z - y)).comp z h1
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have hK : ∀ z y : Space,
      ‖heatG θ y • fderiv ℝ (heatG b) (z - y)‖ ≤ (C * b ^ (-(2:ℝ))) * ‖heatG θ y‖ := by
    intro z y
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hCb b hb (z - y)) (norm_nonneg _)
  have hHas : HasFDerivAt (fun z : Space => ∫ y : Space, heatG θ y * heatG b (z - y))
      (∫ y : Space, heatG θ y • fderiv ℝ (heatG b) (x - y)) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun z y => heatG θ y • fderiv ℝ (heatG b) (z - y))
      (bound := fun y : Space => (C * b ^ (-(2:ℝ))) * ‖heatG θ y‖) (s := univ) univ_mem ?_
      (hF_int x) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall (fun z => ?_)
      exact (((kf3hc_smooth θ).continuous).mul
        ((kf3hc_smooth b).continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · exact (hcont_fd x).aestronglyMeasurable
    · exact ae_of_all _ (fun y z _ => hK z y)
    · exact ((kf3hc_integrable hθ).norm).const_mul _
    · exact ae_of_all _ (fun y z _ => (hcomp z y).const_mul (heatG θ y))
  have hHas' : HasFDerivAt (heatG (θ + b))
      (∫ y : Space, heatG θ y • fderiv ℝ (heatG b) (x - y)) x := by
    rw [← hfun]
    exact hHas
  have hint : Integrable (fun y : Space => heatG θ y • fderiv ℝ (heatG b) (x - y)) :=
    Integrable.mono' ((kf3hc_integrable hθ).norm.const_mul (C * b ^ (-(2:ℝ))))
      (hcont_fd x).aestronglyMeasurable (ae_of_all _ (fun y => hK x y))
  have key := integral_sub_left_eq_self (μ := volume)
    (fun y : Space => heatG θ y * fderiv ℝ (heatG b) (x - y) (UnforcedLeray.coordinateVector j)) x
  simp only [sub_sub_cancel] at key
  rw [hHas'.fderiv, ContinuousLinearMap.integral_apply hint]
  simp only [smul_apply, smul_eq_mul]
  exact key

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
