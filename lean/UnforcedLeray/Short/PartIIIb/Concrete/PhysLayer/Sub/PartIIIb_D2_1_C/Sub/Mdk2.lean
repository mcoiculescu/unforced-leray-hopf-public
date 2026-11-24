import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_1_2

/-!
# `DyMollP`: differentiation of the mollification under the convolution integral

Source: `the November 2 reference manuscript` lines 1351-1362.
`ρ ⋆ Φ` is a convolution with the compactly supported smooth kernel `ρ.normed`, so its
`y_j`-derivative is the convolution with `∂_{y_j} ρ_norm`. The change of variables `w = x - t`
turns this into `∫ -(∂_{y_j} κ_x)(w) Φ_j(w) dw` with `κ_x(w) = ρ_norm(x - w)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem dyMollP : DyMollP := by
  intro ρ Φ hΦ x j
  have hconv : mollP ρ Φ = MeasureTheory.convolution (ρ.normed volume) Φ
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y
    simp [mollP, MeasureTheory.convolution]
  have hκ1 : ContDiff ℝ 1 (ρ.normed volume) := ρ.contDiff_normed.of_le (by exact_mod_cast le_top)
  have hκd : Differentiable ℝ (ρ.normed volume) := hκ1.differentiable (by norm_num)
  have hcf : HasCompactSupport (fderiv ℝ (ρ.normed volume)) :=
    ρ.hasCompactSupport_normed.fderiv (𝕜 := ℝ)
  have hcont : Continuous (fderiv ℝ (ρ.normed volume)) := hκ1.continuous_fderiv (by norm_num)
  have hD := ρ.hasCompactSupport_normed.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hκ1 hΦ x
  rw [← hconv] at hD
  have hR : ∀ w : ℝ × Space, dy j (reflK ρ x) w
      = -(((fderiv ℝ (ρ.normed volume) (x - w)) (0, coordinateVector j) : ℝ) : ℂ) := by
    intro w
    have hsub : HasFDerivAt (fun y : ℝ × Space => x - y) (-ContinuousLinearMap.id ℝ _) w :=
      (hasFDerivAt_id w).const_sub x
    have hc : HasFDerivAt (fun y : ℝ × Space => ρ.normed volume (x - y))
        ((fderiv ℝ (ρ.normed volume) (x - w)).comp (-ContinuousLinearMap.id ℝ _)) w :=
      (hκd (x - w)).hasFDerivAt.comp w hsub
    have hC := Complex.ofRealCLM.hasFDerivAt.comp w hc
    have hfun : reflK ρ x = Complex.ofRealCLM ∘ (fun y : ℝ × Space => ρ.normed volume (x - y)) := by
      funext y
      simp [reflK]
    unfold UnforcedLeray.PhaseSpace.dy
    rw [hfun, hC.fderiv]
    simp
  have hint : Integrable (fun t : ℝ × Space =>
      (ContinuousLinearMap.precompL (ℝ × Space) (ContinuousLinearMap.lsmul ℝ ℝ))
        (fderiv ℝ (ρ.normed volume) t) (Φ (x - t))) volume :=
    (hcf.convolutionExists_left _ hcont hΦ x).integrable
  have hsub : ∀ g : ℝ × Space → ℂ, ∫ t, g t = ∫ w, g (x - w) := fun g =>
    (integral_sub_left_eq_self g volume x).symm
  simp only [hR, neg_neg]
  rw [UnforcedLeray.PhaseSpace.dy, hD.fderiv, MeasureTheory.convolution_def,
    ContinuousLinearMap.integral_apply hint]
  have hc := (PiLp.proj 2 (fun _ : Fin 3 => ℂ) j : CVec3 →L[ℂ] ℂ).integral_comp_comm
    (hint.apply_continuousLinearMap (0, coordinateVector j))
  refine hc.symm.trans ?_
  refine (hsub _).trans ?_
  congr 1
  funext w
  simp [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, sub_sub_cancel]
