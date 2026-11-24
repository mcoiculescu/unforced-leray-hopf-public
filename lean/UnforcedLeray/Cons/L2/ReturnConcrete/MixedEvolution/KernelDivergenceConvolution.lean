import UnforcedLeray.Lib.HeatCylinder.Derivative
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelGradientConvolution

/-!
# The full divergence-kernel composition law

This packages the componentwise Gaussian-gradient identity as the actual B0296 divergence kernel
acting on a fixed two-column tensor. It is the scalar-input-independent kernel identity used in
the eventual periodic Fubini bridge.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open Filter
open scoped ENNReal
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.B0289
open UnforcedLeray.B0296

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

private theorem heatKernel1_abs_le_normalization {θ : ℝ} (hθ : 0 < θ) (x : ℝ) :
    |B0191.heatKernel 1 θ x| ≤ (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ := by
  rw [B0191.heatKernel]
  have hC : 0 ≤ (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ := by positivity
  have hexp : Real.exp (-(x ^ 2) / (4 * 1 * θ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hnum : -(x ^ 2) ≤ 0 := neg_nonpos.mpr (sq_nonneg x)
    have hden : 0 ≤ 4 * 1 * θ := by positivity
    exact div_nonpos_of_nonpos_of_nonneg hnum hden
  rw [abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
  calc
    (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ * Real.exp (-(x ^ 2) / (4 * 1 * θ)) ≤
        (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hexp hC
    _ = _ := by ring

private theorem integrable_gradKernelAbs_toReal {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun w : Plane => (gradKernelAbs θ w).toReal) := by
  have hkmeas : Measurable (fun w : Plane => gradKernelAbs θ w) := measurable_gradKernelAbs θ
  have hkfin : ∀ w : Plane, gradKernelAbs θ w ≠ ∞ := gradKernelAbs_ne_top θ
  refine ⟨hkmeas.ennreal_toReal.aestronglyMeasurable, ?_⟩
  change ∫⁻ w : Plane, ‖(gradKernelAbs θ w).toReal‖ₑ < ∞
  have hnorm : (fun w : Plane => ‖(gradKernelAbs θ w).toReal‖ₑ) = gradKernelAbs θ := by
    funext w
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (ENNReal.toReal_nonneg),
      ENNReal.ofReal_toReal (hkfin w)]
  rw [hnorm, lintegral_gradKernelAbs hθ]
  exact ENNReal.ofReal_lt_top

/-- The actual planar heat kernel times the actual B0296 gradient kernel is integrable in space. -/
private theorem integrable_heatKernel2_smul_gradHeatKernel2 {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (z : Plane) :
    Integrable (fun w : Plane => heatKernel2 α (z - w) • gradHeatKernel2 β w) := by
  have hCq (x : ℝ) : |B0191.heatKernel 1 α (z.1 - x)| ≤
      (Real.sqrt (4 * Real.pi * 1 * α))⁻¹ := heatKernel1_abs_le_normalization hα _
  have hCη (x : ℝ) : |B0191.heatKernel 1 α (z.2 - x)| ≤
      (Real.sqrt (4 * Real.pi * 1 * α))⁻¹ := heatKernel1_abs_le_normalization hα _
  have hgrad1 : Integrable (fun w : Plane => heatKernel2 α (z - w) *
      (gradHeatKernel2 β w).1) := by
    have hd : Integrable (fun w : ℝ => dHeatKernel β w) := integrable_dHeatKernel hβ
    have hq : Integrable (fun x : ℝ => B0191.heatKernel 1 α (z.1 - x) * dHeatKernel β x) := by
      have hbdd : ∀ᵐ x ∂volume, ‖B0191.heatKernel 1 α (z.1 - x)‖ ≤
          (Real.sqrt (4 * Real.pi * 1 * α))⁻¹ := by
        filter_upwards [] with x
        rw [Real.norm_eq_abs]
        exact hCq x
      have hcont : AEStronglyMeasurable (fun x : ℝ => B0191.heatKernel 1 α (z.1 - x)) :=
        ((continuous_heatKernel1 α).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      have hmul := hd.bdd_mul hcont (c := (Real.sqrt (4 * Real.pi * 1 * α))⁻¹) hbdd
      refine hmul.congr (Eventually.of_forall fun x => ?_)
      ring
    have hη : Integrable (fun x : ℝ => B0191.heatKernel 1 α (z.2 - x) *
        B0191.heatKernel 1 β x) :=
      (integrable_heatKernel1_conv hα hβ z.2).congr (Eventually.of_forall fun x => by
        simp only [sub_eq_add_neg])
    have hprod := hq.mul_prod hη
    have hfactor : (fun w : Plane => heatKernel2 α (z - w) *
        (gradHeatKernel2 β w).1) = fun w =>
          (B0191.heatKernel 1 α (z.1 - w.1) * dHeatKernel β w.1) *
            (B0191.heatKernel 1 α (z.2 - w.2) * B0191.heatKernel 1 β w.2) := by
      funext w
      simp [heatKernel2, gradHeatKernel2, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [hfactor]
    exact hprod
  have hgrad2 : Integrable (fun w : Plane => heatKernel2 α (z - w) *
      (gradHeatKernel2 β w).2) := by
    have hη : Integrable (fun x : ℝ => B0191.heatKernel 1 α (z.2 - x) * dHeatKernel β x) := by
      have hd : Integrable (fun x : ℝ => dHeatKernel β x) := integrable_dHeatKernel hβ
      have hbdd : ∀ᵐ x ∂volume, ‖B0191.heatKernel 1 α (z.2 - x)‖ ≤
          (Real.sqrt (4 * Real.pi * 1 * α))⁻¹ := by
        filter_upwards [] with x
        rw [Real.norm_eq_abs]
        exact hCη x
      have hcont : AEStronglyMeasurable (fun x : ℝ => B0191.heatKernel 1 α (z.2 - x)) :=
        ((continuous_heatKernel1 α).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      have hmul := hd.bdd_mul hcont (c := (Real.sqrt (4 * Real.pi * 1 * α))⁻¹) hbdd
      refine hmul.congr (Eventually.of_forall fun x => ?_)
      ring
    have hq : Integrable (fun x : ℝ => B0191.heatKernel 1 α (z.1 - x) *
        B0191.heatKernel 1 β x) :=
      (integrable_heatKernel1_conv hα hβ z.1).congr (Eventually.of_forall fun x => by
        simp only [sub_eq_add_neg])
    have hprod := hq.mul_prod hη
    have hfactor : (fun w : Plane => heatKernel2 α (z - w) *
        (gradHeatKernel2 β w).2) = fun w =>
          (B0191.heatKernel 1 α (z.1 - w.1) * B0191.heatKernel 1 β w.1) *
            (B0191.heatKernel 1 α (z.2 - w.2) * dHeatKernel β w.2) := by
      funext w
      simp [heatKernel2, gradHeatKernel2, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [hfactor]
    exact hprod
  have hpair : Integrable (fun w : Plane =>
      (heatKernel2 α (z - w) * (gradHeatKernel2 β w).1,
       heatKernel2 α (z - w) * (gradHeatKernel2 β w).2)) := hgrad1.prodMk hgrad2
  have hEq : (fun w : Plane => heatKernel2 α (z - w) • gradHeatKernel2 β w) =
      fun w => (heatKernel2 α (z - w) * (gradHeatKernel2 β w).1,
        heatKernel2 α (z - w) * (gradHeatKernel2 β w).2) := by
    funext w
    rfl
  exact hpair.congr (Eventually.of_forall fun w => (congrFun hEq w).symm)

/-- The scalar heat kernel composed with the actual B0296 divergence kernel is the summed-age
divergence kernel, on every fixed two-column tensor. -/
theorem integral_heatKernel2_divKernel_conv {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (z : Plane) (x : Plane × Plane) :
    ∫ w : Plane, heatKernel2 α (z - w) • divKernel β w x =
      divKernel (α + β) z x := by
  let Lx : (ℝ × ℝ) →L[ℝ] Plane :=
    (ContinuousLinearMap.toSpanSingleton ℝ x.1).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (ContinuousLinearMap.toSpanSingleton ℝ x.2).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hgradInt := integrable_heatKernel2_smul_gradHeatKernel2 hα hβ z
  have hgrad : ∫ w : Plane, heatKernel2 α (z - w) • gradHeatKernel2 β w =
      gradHeatKernel2 (α + β) z := by
    apply Prod.ext
    · rw [fst_integral hgradInt]
      have h := integral_heatKernel2_gradHeatKernel2_conv_fst hα hβ z
      simpa [smul_eq_mul] using h
    · rw [snd_integral hgradInt]
      have h := integral_heatKernel2_gradHeatKernel2_conv_snd hα hβ z
      simpa [smul_eq_mul] using h
  have hfun : (fun w : Plane => heatKernel2 α (z - w) • divKernel β w x) =
      fun w => Lx (heatKernel2 α (z - w) • gradHeatKernel2 β w) := by
    funext w
    simp [Lx, divKernel, ContinuousLinearMap.comp_apply, smul_eq_mul, mul_smul]
  calc
    ∫ w : Plane, heatKernel2 α (z - w) • divKernel β w x =
        Lx (∫ w : Plane, heatKernel2 α (z - w) • gradHeatKernel2 β w) := by
          rw [hfun, Lx.integral_comp_comm hgradInt]
    _ = divKernel (α + β) z x := by
          rw [hgrad]
          simp [Lx, divKernel, ContinuousLinearMap.comp_apply, smul_eq_mul]

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.integral_heatKernel2_divKernel_conv
