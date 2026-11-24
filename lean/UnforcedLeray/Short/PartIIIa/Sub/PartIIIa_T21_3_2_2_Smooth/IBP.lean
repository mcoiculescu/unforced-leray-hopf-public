import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.Basic
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeIntegrable
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeDerivative
import UnforcedLeray.Units.B0296.Kernel

/-!
# Part III-a, `PartIII-a:T21/3/2/2/org`: Gaussian integration by parts

Source of record: `the November 2 reference manuscript`, lines 2819-2836.

The age derivative of B0284's planar kernel splits as `∂_θ G_θ = ∂_q² G_θ + ∂_η² G_θ`; two
whole-plane integrations by parts move both derivatives onto a cylinder test:
`∫ ∂_θ G_θ(w) ψ(z - w) dw = ∫ G_θ(w) Δψ(z - w) dw`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.B0284 (heatKernel2)

/-- Whole-plane integration by parts moving one derivative from an integrable kernel `K` (with
integrable directional derivative) onto a bounded `C¹` function with bounded derivative. -/
theorem integral_kernel_fderiv_mul_comp_sub {K : ℝ × ℝ → ℝ} (hKdiff : Differentiable ℝ K)
    (hK : Integrable K) (e : ℝ × ℝ) (hKe : Integrable (fun w => fderiv ℝ K w e))
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M N : ℝ} (hfb : ∀ x, |f x| ≤ M)
    (hdfb : ∀ x, ‖fderiv ℝ f x‖ ≤ N) (z : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, fderiv ℝ K w e * f (z - w) = ∫ w : ℝ × ℝ, K w * fderiv ℝ f (z - w) e := by
  let G : ℝ × ℝ → ℝ := fun w => f (z - w)
  have hGcd : ContDiff ℝ 1 G := hf.comp (contDiff_const.sub contDiff_id)
  have hGcont : Continuous G := hGcd.continuous
  have hGbound : ∀ w, ‖G w‖ ≤ M := fun w => by
    rw [Real.norm_eq_abs]
    exact hfb (z - w)
  have hGdiff : Differentiable ℝ G := hGcd.differentiable one_ne_zero
  have hGderiv (w : ℝ × ℝ) : fderiv ℝ G w e = -(fderiv ℝ f (z - w) e) := by
    have hmap : HasFDerivAt (fun y : ℝ × ℝ => z - y)
        (-ContinuousLinearMap.id ℝ (ℝ × ℝ)) w := (hasFDerivAt_id w).const_sub z
    have hcomp := ((hf.differentiable one_ne_zero) (z - w)).hasFDerivAt.comp w hmap
    change fderiv ℝ (f ∘ (fun y : ℝ × ℝ => z - y)) w e = _
    rw [hcomp.fderiv]
    simp
  have hGderivBound : ∀ w, ‖fderiv ℝ G w e‖ ≤ N * ‖e‖ := by
    intro w
    rw [hGderiv w, norm_neg]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hdfb (z - w)) (norm_nonneg _))
  have hGderivCont : Continuous (fun w => fderiv ℝ G w e) :=
    (hGcd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hI1' : Integrable (fun w => G w * fderiv ℝ K w e) :=
    hKe.bdd_mul hGcont.aestronglyMeasurable (c := M) (Eventually.of_forall hGbound)
  have hI1 : Integrable (fun w => fderiv ℝ K w e * G w) :=
    hI1'.congr (Eventually.of_forall fun w => mul_comm (G w) _)
  have hI2' : Integrable (fun w => fderiv ℝ G w e * K w) :=
    hK.bdd_mul hGderivCont.aestronglyMeasurable (c := N * ‖e‖)
      (Eventually.of_forall hGderivBound)
  have hI2 : Integrable (fun w => K w * fderiv ℝ G w e) :=
    hI2'.congr (Eventually.of_forall fun w => mul_comm _ _)
  have hI3' : Integrable (fun w => G w * K w) :=
    hK.bdd_mul hGcont.aestronglyMeasurable (c := M) (Eventually.of_forall hGbound)
  have hI3 : Integrable (fun w => K w * G w) :=
    hI3'.congr (Eventually.of_forall fun w => mul_comm _ _)
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hI1 hI2 hI3 (fun w _ => hKdiff w) (fun w _ => hGdiff w)
  have hIBP' : ∫ w, K w * fderiv ℝ G w e = -∫ w, fderiv ℝ K w e * G w := hIBP
  rw [show (fun w : ℝ × ℝ => fderiv ℝ K w e * f (z - w)) =
      fun w => fderiv ℝ K w e * G w from rfl,
    show (fun w : ℝ × ℝ => K w * fderiv ℝ f (z - w) e) =
      fun w => -(K w * fderiv ℝ G w e) from funext fun w => by
        rw [hGderiv w]
        ring]
  rw [integral_neg, hIBP']
  ring

/-! ### The one-dimensional kernel and its first two derivatives -/

/-- The second derivative `G_θ''(x) = (x²/(4θ²) - 1/(2θ)) G_θ(x)` of the one-dimensional kernel. -/
def ddHeatKernel (θ x : ℝ) : ℝ :=
  (x ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * UnforcedLeray.B0191.heatKernel 1 θ x

theorem hasDerivAt_dHeatKernel' {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    HasDerivAt (UnforcedLeray.B0296.dHeatKernel θ) (ddHeatKernel θ x) x := by
  have h := (((hasDerivAt_id x).div_const (2 * θ)).neg).mul
    (UnforcedLeray.B0296.hasDerivAt_heatKernel hθ x)
  refine h.congr_deriv ?_
  show -(1 / (2 * θ)) * UnforcedLeray.B0191.heatKernel 1 θ x +
      -(x / (2 * θ)) * UnforcedLeray.B0296.dHeatKernel θ x = ddHeatKernel θ x
  rw [UnforcedLeray.B0296.dHeatKernel, ddHeatKernel]
  ring

theorem differentiable_heatKernel1 (θ : ℝ) :
    Differentiable ℝ (UnforcedLeray.B0191.heatKernel 1 θ) :=
  (UnforcedLeray.B0191.contDiff_heatKernel 1 θ).differentiable (by simp)

theorem integrable_ddHeatKernel {θ : ℝ} (hθ : 0 < θ) : Integrable (ddHeatKernel θ) := by
  have h := ((UnforcedLeray.HeatCylinder.integrable_sq_mul_heatKernel1 hθ).const_mul
    (1 / (4 * θ ^ 2))).sub ((UnforcedLeray.B0296.integrable_heatKernel1 hθ).const_mul
      (1 / (2 * θ)))
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [ddHeatKernel, Pi.sub_apply]
  ring

/-! ### Directional derivatives of a product kernel -/

theorem fderiv_apply_q_of_hasDerivAt {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (w : ℝ × ℝ)
    {d : ℝ} (h : HasDerivAt (fun x => F (x, w.2)) d w.1) :
    fderiv ℝ F w ((1 : ℝ), (0 : ℝ)) = d := by
  have h0 : HasDerivAt (fun q : ℝ => (q, w.2)) ((1 : ℝ), (0 : ℝ)) w.1 :=
    (hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2)
  have h1 := (hF (w.1, w.2)).hasFDerivAt.comp_hasDerivAt w.1 h0
  exact h1.unique h

theorem fderiv_apply_eta_of_hasDerivAt {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (w : ℝ × ℝ)
    {d : ℝ} (h : HasDerivAt (fun y => F (w.1, y)) d w.2) :
    fderiv ℝ F w ((0 : ℝ), (1 : ℝ)) = d := by
  have h0 : HasDerivAt (fun y : ℝ => (w.1, y)) ((0 : ℝ), (1 : ℝ)) w.2 :=
    (hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2)
  have h1 := (hF (w.1, w.2)).hasFDerivAt.comp_hasDerivAt w.2 h0
  exact h1.unique h

theorem dir_zero' : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := by simp [B0579.dir]

theorem dir_one' : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := by simp [B0579.dir]

/-- `∫ ∂_θ G_θ(w) ψ(z - w) dw = ∫ G_θ(w) Δψ(z - w) dw` for a cylinder test `ψ` (`θ > 0`). -/
theorem integral_ageDeriv_mul_comp_sub {θ : ℝ} (hθ : 0 < θ) {c : ℝ} (hc : 0 < c)
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) (z : ℝ × ℝ) :
    ∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * ψ (z - w) =
      ∫ w : ℝ × ℝ, heatKernel2 θ w * lapP ψ (z - w) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  let g : ℝ → ℝ := UnforcedLeray.B0191.heatKernel 1 θ
  let dg : ℝ → ℝ := UnforcedLeray.B0296.dHeatKernel θ
  let ddg : ℝ → ℝ := ddHeatKernel θ
  have hg : Differentiable ℝ g := differentiable_heatKernel1 θ
  have hdg : Differentiable ℝ dg := fun x => (hasDerivAt_dHeatKernel' hθ0 x).differentiableAt
  have hgI : Integrable g := UnforcedLeray.B0296.integrable_heatKernel1 hθ
  have hdgI : Integrable dg := UnforcedLeray.B0296.integrable_dHeatKernel hθ
  have hddgI : Integrable ddg := integrable_ddHeatKernel hθ
  let K : ℝ × ℝ → ℝ := heatKernel2 θ
  let Kq : ℝ × ℝ → ℝ := fun w => dg w.1 * g w.2
  let Ke : ℝ × ℝ → ℝ := fun w => g w.1 * dg w.2
  let Kqq : ℝ × ℝ → ℝ := fun w => ddg w.1 * g w.2
  let Kee : ℝ × ℝ → ℝ := fun w => g w.1 * ddg w.2
  have hKdiff : Differentiable ℝ K := by
    show Differentiable ℝ (fun w : ℝ × ℝ => g w.1 * g w.2)
    exact (hg.comp differentiable_fst).mul (hg.comp differentiable_snd)
  have hKqdiff : Differentiable ℝ Kq := (hdg.comp differentiable_fst).mul (hg.comp differentiable_snd)
  have hKediff : Differentiable ℝ Ke := (hg.comp differentiable_fst).mul (hdg.comp differentiable_snd)
  have hKI : Integrable K := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hKqI : Integrable Kq := hdgI.mul_prod hgI
  have hKeI : Integrable Ke := hgI.mul_prod hdgI
  have hKqqI : Integrable Kqq := hddgI.mul_prod hgI
  have hKeeI : Integrable Kee := hgI.mul_prod hddgI
  -- directional derivatives of the kernels
  have hK_q : ∀ w, fderiv ℝ K w ((1 : ℝ), (0 : ℝ)) = Kq w := fun w =>
    fderiv_apply_q_of_hasDerivAt hKdiff w
      ((UnforcedLeray.B0296.hasDerivAt_heatKernel hθ0 w.1).mul_const (g w.2))
  have hK_e : ∀ w, fderiv ℝ K w ((0 : ℝ), (1 : ℝ)) = Ke w := fun w =>
    fderiv_apply_eta_of_hasDerivAt hKdiff w
      ((UnforcedLeray.B0296.hasDerivAt_heatKernel hθ0 w.2).const_mul (g w.1))
  have hKq_q : ∀ w, fderiv ℝ Kq w ((1 : ℝ), (0 : ℝ)) = Kqq w := fun w =>
    fderiv_apply_q_of_hasDerivAt hKqdiff w ((hasDerivAt_dHeatKernel' hθ0 w.1).mul_const (g w.2))
  have hKe_e : ∀ w, fderiv ℝ Ke w ((0 : ℝ), (1 : ℝ)) = Kee w := fun w =>
    fderiv_apply_eta_of_hasDerivAt hKediff w
      ((hasDerivAt_dHeatKernel' hθ0 w.2).const_mul (g w.1))
  have hKqI' : Integrable (fun w => fderiv ℝ K w ((1 : ℝ), (0 : ℝ))) :=
    hKqI.congr (Eventually.of_forall fun w => (hK_q w).symm)
  have hKeI' : Integrable (fun w => fderiv ℝ K w ((0 : ℝ), (1 : ℝ))) :=
    hKeI.congr (Eventually.of_forall fun w => (hK_e w).symm)
  have hKqqI' : Integrable (fun w => fderiv ℝ Kq w ((1 : ℝ), (0 : ℝ))) :=
    hKqqI.congr (Eventually.of_forall fun w => (hKq_q w).symm)
  have hKeeI' : Integrable (fun w => fderiv ℝ Ke w ((0 : ℝ), (1 : ℝ))) :=
    hKeeI.congr (Eventually.of_forall fun w => (hKe_e w).symm)
  -- bounds on the test and its derivatives
  have hC1 : ∀ {φ : ℝ × ℝ → ℝ}, B0579.IsCylTest c φ → ContDiff ℝ 1 φ :=
    fun hφ => hφ.smooth.of_le (by simp)
  obtain ⟨M, _, hM⟩ := cylTest_exists_bound hc hψ
  obtain ⟨N, _, hN⟩ := cylTest_exists_fderiv_bound hc hψ
  obtain ⟨M0, _, hM0⟩ := cylTest_exists_bound hc (hψ.pd 0)
  obtain ⟨N0, _, hN0⟩ := cylTest_exists_fderiv_bound hc (hψ.pd 0)
  obtain ⟨M1, _, hM1⟩ := cylTest_exists_bound hc (hψ.pd 1)
  obtain ⟨N1, _, hN1⟩ := cylTest_exists_fderiv_bound hc (hψ.pd 1)
  obtain ⟨M00, _, hM00⟩ := cylTest_exists_bound hc ((hψ.pd 0).pd 0)
  obtain ⟨M11, _, hM11⟩ := cylTest_exists_bound hc ((hψ.pd 1).pd 1)
  have hpd0 : ∀ (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ),
      fderiv ℝ φ x ((1 : ℝ), (0 : ℝ)) = B0579.pd 0 φ x := fun φ x => by
    simp only [B0579.pd, dir_zero']
  have hpd1 : ∀ (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ),
      fderiv ℝ φ x ((0 : ℝ), (1 : ℝ)) = B0579.pd 1 φ x := fun φ x => by
    simp only [B0579.pd, dir_one']
  have hbddMul : ∀ {k : ℝ × ℝ → ℝ}, Integrable k → ∀ {φ : ℝ × ℝ → ℝ}, Continuous φ →
      ∀ {B : ℝ}, (∀ x, |φ x| ≤ B) → Integrable (fun w => k w * φ (z - w)) := by
    intro k hk φ hφ B hB
    have h := hk.bdd_mul (hφ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (c := B) (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        exact hB (z - w))
    exact h.congr (Eventually.of_forall fun w => mul_comm _ _)
  -- the q-direction: two integrations by parts
  have hq : ∫ w : ℝ × ℝ, Kqq w * ψ (z - w) =
      ∫ w : ℝ × ℝ, K w * B0579.pd 0 (B0579.pd 0 ψ) (z - w) := by
    have s1 := integral_kernel_fderiv_mul_comp_sub hKqdiff hKqI _ hKqqI' (hC1 hψ) hM hN z
    have s2 := integral_kernel_fderiv_mul_comp_sub hKdiff hKI _ hKqI' (hC1 (hψ.pd 0)) hM0 hN0 z
    simp only [hKq_q, hK_q, hpd0] at s1 s2
    rw [s1, s2]
  have he : ∫ w : ℝ × ℝ, Kee w * ψ (z - w) =
      ∫ w : ℝ × ℝ, K w * B0579.pd 1 (B0579.pd 1 ψ) (z - w) := by
    have s1 := integral_kernel_fderiv_mul_comp_sub hKediff hKeI _ hKeeI' (hC1 hψ) hM hN z
    have s2 := integral_kernel_fderiv_mul_comp_sub hKdiff hKI _ hKeI' (hC1 (hψ.pd 1)) hM1 hN1 z
    simp only [hKe_e, hK_e, hpd1] at s1 s2
    rw [s1, s2]
  have hsplit : ∀ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * ψ (z - w) =
      Kqq w * ψ (z - w) + Kee w * ψ (z - w) := by
    intro w
    simp only [UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative, Kqq, Kee, ddg, g,
      ddHeatKernel, UnforcedLeray.B0284.heatKernel2]
    ring
  simp_rw [hsplit]
  rw [integral_add (hbddMul hKqqI hψ.continuous hM) (hbddMul hKeeI hψ.continuous hM), hq, he,
    ← integral_add (hbddMul hKI ((hψ.pd 0).pd 0).continuous hM00)
      (hbddMul hKI ((hψ.pd 1).pd 1).continuous hM11)]
  congr 1
  funext w
  simp only [lapP, K]
  ring

end UnforcedLeray.Short.IIIa.Exist
