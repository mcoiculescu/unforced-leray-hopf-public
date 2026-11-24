import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1_2
import UnforcedLeray.Lib.TrainB.P0GaussianTensorIBP
import UnforcedLeray.Lib.HeatCylinder.SmoothBounds

/-!
# `smoothRowDivHeatPointwise`: row-divergence heat, pointwise

Source of record: `the November 2 reference manuscript`, lines 3594-3625.

The target `smoothRowDivHeatPointwise : SmoothRowDivHeatPointwise` quantifies over periods `0 < c`
only. For such `c` the cylinder-smooth field `S` is bounded together with its first derivative
(`exists_global_bound_of_cylSmooth`, `exists_global_deriv_bound_of_cylSmooth`), which is what the
library Gaussian integration by parts needs. The proof of the case `c ≠ 0` is
`heatDiv_eq_heat_rowDiv_of_ne_zero` below; the target follows from it with `hc.ne'`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

private theorem sRDH_int_q {θ : ℝ} (hθ : 0 < θ) {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M) (z : Plane) :
    Integrable (fun w : Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * f (z - w)) := by
  obtain ⟨M, -, hM⟩ := hfb
  have hGcont : Continuous (fun w : Plane => f (z - w)) :=
    hf.continuous.comp (continuous_const.sub continuous_id)
  have hGbound : ∀ w, ‖f (z - w)‖ ≤ M := fun w => hM (z - w)
  have hKq : Integrable (fun w : Plane =>
      UnforcedLeray.B0296.dHeatKernel θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2) := by
    exact (UnforcedLeray.B0296.integrable_dHeatKernel hθ).mul_prod
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
  have hi0 := hKq.bdd_mul hGcont.aestronglyMeasurable (c := M)
    (Filter.Eventually.of_forall hGbound)
  refine hi0.congr (Filter.Eventually.of_forall fun w => ?_)
  simp [UnforcedLeray.B0296.gradHeatKernel2]
  ring

private theorem sRDH_int_eta {θ : ℝ} (hθ : 0 < θ) {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M) (z : Plane) :
    Integrable (fun w : Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * f (z - w)) := by
  obtain ⟨M, -, hM⟩ := hfb
  have hGcont : Continuous (fun w : Plane => f (z - w)) :=
    hf.continuous.comp (continuous_const.sub continuous_id)
  have hGbound : ∀ w, ‖f (z - w)‖ ≤ M := fun w => hM (z - w)
  have hKeta : Integrable (fun w : Plane =>
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0296.dHeatKernel θ w.2) := by
    exact (UnforcedLeray.B0296.integrable_heatKernel1 hθ).mul_prod
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
  have hi := hKeta.bdd_mul hGcont.aestronglyMeasurable (c := M)
    (Filter.Eventually.of_forall hGbound)
  refine hi.congr (Filter.Eventually.of_forall fun w => ?_)
  simp [UnforcedLeray.B0296.gradHeatKernel2]
  ring

private theorem sRDH_int_deriv {θ : ℝ} (hθ : 0 < θ) {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hdfb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ M) (z e : Plane) :
    Integrable (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w *
      fderiv ℝ f (z - w) e) := by
  obtain ⟨M, -, hM⟩ := hdfb
  have hK := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hmap : ContDiff ℝ 1 (fun w : Plane => z - w) := by
    exact contDiff_const.sub contDiff_id
  have hsmooth : ContDiff ℝ 1 (fun w : Plane => f (z - w)) :=
    hf.of_le (by norm_num) |>.comp hmap
  have hGcont : Continuous (fun w : Plane => fderiv ℝ (fun y : Plane => f (z - y)) w e) :=
    (hsmooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hGbound : ∀ w, ‖fderiv ℝ f (z - w) e‖ ≤ M * ‖e‖ := by
    intro w
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hM (z - w)) (norm_nonneg _))
  have hGderiv (w : Plane) :
      fderiv ℝ (fun y : Plane => f (z - y)) w e =
        -(fderiv ℝ f (z - w) e) := by
    have hmap' : HasFDerivAt (fun y : Plane => z - y)
        (-ContinuousLinearMap.id ℝ Plane) w := (hasFDerivAt_id w).const_sub z
    have hcomp := (hf.differentiable (by simp) (z - w)).hasFDerivAt.comp w hmap'
    have hcomp' := hcomp.fderiv
    change fderiv ℝ (fun y : Plane => f (z - y)) w = _ at hcomp'
    rw [hcomp']
    simp
  have hGbound' : ∀ w,
      ‖fderiv ℝ (fun y : Plane => f (z - y)) w e‖ ≤ M * ‖e‖ := by
    intro w
    rw [hGderiv, norm_neg]
    exact hGbound w
  have hi := hK.bdd_mul hGcont.aestronglyMeasurable (c := M * ‖e‖)
    (Filter.Eventually.of_forall hGbound')
  refine hi.neg.congr (Filter.Eventually.of_forall fun w => ?_)
  change -((fderiv ℝ (fun y : Plane => f (z - y)) w e) *
      UnforcedLeray.B0284.heatKernel2 θ w) = _
  rw [hGderiv w]
  ring

/-- Gaussian integration by parts with the period `c ≠ 0` bounds (source 3594-3625). -/
theorem heatDiv_eq_heat_rowDiv_of_ne_zero {c θ : ℝ} (hc : c ≠ 0) (hθ : 0 < θ)
    (S : Plane → Plane × Plane) (hS : UnforcedLeray.Sob.IsCylSmooth c S) (z : Plane) :
    UnforcedLeray.B0296.heatDiv θ S z = UnforcedLeray.B0284.heat θ (rowDivergence S) z := by
  -- period |c| > 0
  have hP : UnforcedLeray.Sob.IsCylSmooth |c| S := by
    refine ⟨hS.smooth, ?_, hS.bounded⟩
    intro y
    rcases abs_choice c with h | h
    · rw [h]
      exact hS.periodic y
    · rw [h]
      have h2 := hS.periodic (y + (-c, 0))
      have e : y + (-c, 0) + (c, 0) = y := by ext <;> simp
      rw [e] at h2
      exact h2.symm
  have hpos : 0 < |c| := abs_pos.mpr hc
  obtain ⟨M0, hM0nn, hM0⟩ :=
    UnforcedLeray.HeatCylinder.exists_global_bound_of_cylSmooth hpos hP
  obtain ⟨M1, hM1nn, hM1⟩ :=
    UnforcedLeray.HeatCylinder.exists_global_deriv_bound_of_cylSmooth hpos hP
  have hSC : ContDiff ℝ ∞ S := hS.smooth
  have hval : ∀ L : Plane × Plane →L[ℝ] ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖L (S x)‖ ≤ M :=
    fun L => ⟨‖L‖ * M0, mul_nonneg (norm_nonneg _) hM0nn, fun x =>
      (L.le_opNorm (S x)).trans (mul_le_mul_of_nonneg_left (hM0 x) (norm_nonneg _))⟩
  have hder : ∀ L : Plane × Plane →L[ℝ] ℝ,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ (fun y => L (S y)) x‖ ≤ M :=
    fun L => ⟨‖L‖ * M1, mul_nonneg (norm_nonneg _) hM1nn, fun x => by
      have hd : HasFDerivAt S (fderiv ℝ S x) x :=
        ((hSC.differentiable (by simp)) x).hasFDerivAt
      have h2 : HasFDerivAt (fun y => L (S y)) (L.comp (fderiv ℝ S x)) x :=
        L.hasFDerivAt.comp x hd
      rw [h2.fderiv]
      exact (L.opNorm_comp_le (fderiv ℝ S x)).trans
        (mul_le_mul_of_nonneg_left (hM1 x) (norm_nonneg _))⟩
  have hcd : ∀ L : Plane × Plane →L[ℝ] ℝ, ContDiff ℝ ∞ (fun y => L (S y)) :=
    fun L => L.contDiff.comp hSC
  -- the four scalar components
  let L11 : Plane × Plane →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane Plane)
  let L12 : Plane × Plane →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane Plane)
  let L21 : Plane × Plane →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Plane Plane)
  let L22 : Plane × Plane →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Plane Plane)
  have hf11 : ContDiff ℝ ∞ (fun x => (S x).1.1) := hcd L11
  have hf12 : ContDiff ℝ ∞ (fun x => (S x).1.2) := hcd L12
  have hf21 : ContDiff ℝ ∞ (fun x => (S x).2.1) := hcd L21
  have hf22 : ContDiff ℝ ∞ (fun x => (S x).2.2) := hcd L22
  have hb11 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖(S x).1.1‖ ≤ M := hval L11
  have hb12 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖(S x).1.2‖ ≤ M := hval L12
  have hb21 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖(S x).2.1‖ ≤ M := hval L21
  have hb22 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖(S x).2.2‖ ≤ M := hval L22
  have hd11 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ (fun x => (S x).1.1) x‖ ≤ M := hder L11
  have hd12 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ (fun x => (S x).1.2) x‖ ≤ M := hder L12
  have hd21 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ (fun x => (S x).2.1) x‖ ≤ M := hder L21
  have hd22 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ (fun x => (S x).2.2) x‖ ≤ M := hder L22
  -- Gaussian integration by parts, one scalar pair per output coordinate
  have N1a := UnforcedLeray.TrainB.integral_gradKernel_row_eq_integral_kernel_rowDiv hθ
    hf11 hf21 hb11 hb21 hd11 hd21 z
  have N1b := UnforcedLeray.TrainB.integral_gradKernel_row_eq_integral_kernel_rowDiv hθ
    hf12 hf22 hb12 hb22 hd12 hd22 z
  -- integrability of the two output coordinates on each side
  have hA1 : Integrable (fun w : Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * (S (z - w)).1.1 +
        (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * (S (z - w)).2.1) :=
    (sRDH_int_q hθ hf11 hb11 z).add (sRDH_int_eta hθ hf21 hb21 z)
  have hA2 : Integrable (fun w : Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * (S (z - w)).1.2 +
        (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * (S (z - w)).2.2) :=
    (sRDH_int_q hθ hf12 hb12 z).add (sRDH_int_eta hθ hf22 hb22 z)
  have hB1 : Integrable (fun w : Plane =>
      UnforcedLeray.B0284.heatKernel2 θ w *
        (fderiv ℝ (fun x => (S x).1.1) (z - w) (1, 0) +
          fderiv ℝ (fun x => (S x).2.1) (z - w) (0, 1))) := by
    simp only [mul_add]
    exact (sRDH_int_deriv hθ hf11 hd11 z (1, 0)).add
      (sRDH_int_deriv hθ hf21 hd21 z (0, 1))
  have hB2 : Integrable (fun w : Plane =>
      UnforcedLeray.B0284.heatKernel2 θ w *
        (fderiv ℝ (fun x => (S x).1.2) (z - w) (1, 0) +
          fderiv ℝ (fun x => (S x).2.2) (z - w) (0, 1))) := by
    simp only [mul_add]
    exact (sRDH_int_deriv hθ hf12 hd12 z (1, 0)).add
      (sRDH_int_deriv hθ hf22 hd22 z (0, 1))
  -- pointwise identities of the integrands
  have e1 : ∀ w : Plane, UnforcedLeray.B0296.divKernel θ w (S (z - w)) =
      ((UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * (S (z - w)).1.1 +
          (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * (S (z - w)).2.1,
        (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * (S (z - w)).1.2 +
          (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * (S (z - w)).2.2) := by
    intro w
    ext <;> simp [UnforcedLeray.B0296.divKernel]
  have e2 : ∀ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w • rowDivergence S (z - w) =
      (UnforcedLeray.B0284.heatKernel2 θ w *
          (fderiv ℝ (fun x => (S x).1.1) (z - w) (1, 0) +
            fderiv ℝ (fun x => (S x).2.1) (z - w) (0, 1)),
        UnforcedLeray.B0284.heatKernel2 θ w *
          (fderiv ℝ (fun x => (S x).1.2) (z - w) (1, 0) +
            fderiv ℝ (fun x => (S x).2.2) (z - w) (0, 1))) := by
    intro w
    ext <;> simp [rowDivergence]
  rw [UnforcedLeray.B0296.heatDiv_apply_of_pos hθ S z,
    UnforcedLeray.B0284.heat_apply_of_pos hθ (rowDivergence S) z]
  simp only [e1, e2]
  rw [integral_pair hA1 hA2, integral_pair hB1 hB2]
  exact Prod.ext N1a N1b

theorem smoothRowDivHeatPointwise : SmoothRowDivHeatPointwise := by
  intro c θ hc hθ S hS z
  exact heatDiv_eq_heat_rowDiv_of_ne_zero hc.ne' hθ S hS z

end UnforcedLeray.Short.PartI
