import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz.Rho

/-!
# Leibniz rules for the Cartesian Laplacian (`TCLeibniz` leaves)

Source `the November 2 reference manuscript` 3700-3712 (`[Δ, 𝒞_y]`):
`Δ(φ V) = (Δφ) V + 2 ∇φ·∇V + φ ΔV` and additivity of `Δ`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcle_diff_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {y : Space} (hf : ContDiffAt ℝ 2 f y) (w : Space) :
    DifferentiableAt ℝ (fun y' => fderiv ℝ f y' w) y :=
  ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
    (by norm_num)

theorem tcle_physLap_add {f g : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y)
    (hg : ContDiffAt ℝ 2 g y) :
    physLap (fun y' => f y' + g y') y = physLap f y + physLap g y := by
  unfold physLap
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold physPd2 physPd
  have hev : ∀ᶠ y' in nhds y, DifferentiableAt ℝ f y' ∧ DifferentiableAt ℝ g y' := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y' h1 h2
    exact ⟨h1.differentiableAt (by norm_num), h2.differentiableAt (by norm_num)⟩
  have heq : (fun y' => fderiv ℝ (fun y' => f y' + g y') y' (coordinateVector j)) =ᶠ[nhds y]
      fun y' => fderiv ℝ f y' (coordinateVector j) + fderiv ℝ g y' (coordinateVector j) := by
    filter_upwards [hev] with y' ⟨h1, h2⟩
    rw [fderiv_fun_add h1 h2]
    rfl
  rw [heq.fderiv_eq, fderiv_fun_add (tcle_diff_fderiv_apply hf _) (tcle_diff_fderiv_apply hg _)]
  rfl

theorem tcle_lap_smul {φ : Space → ℝ} {V : Space → Space} {y : Space} (hφ : ContDiffAt ℝ 2 φ y)
    (hV : ContDiffAt ℝ 2 V y) :
    physLap (fun y' => φ y' • V y') y =
      tcleLapS φ y • V y +
        (2 : ℝ) • ∑ j : Fin 3, fderiv ℝ φ y (coordinateVector j) • fderiv ℝ V y (coordinateVector j) +
          φ y • physLap V y := by
  have hφd : DifferentiableAt ℝ φ y := hφ.differentiableAt (by norm_num)
  have hVd : DifferentiableAt ℝ V y := hV.differentiableAt (by norm_num)
  have hterm : ∀ j : Fin 3, physPd2 (fun y' => φ y' • V y') j j y =
      (fderiv ℝ (fun y' => fderiv ℝ φ y' (coordinateVector j)) y (coordinateVector j)) • V y +
        ((2 : ℝ) • (fderiv ℝ φ y (coordinateVector j) • fderiv ℝ V y (coordinateVector j))) +
          φ y • physPd2 V j j y := by
    intro j
    unfold physPd2 physPd
    have hev : ∀ᶠ y' in nhds y, DifferentiableAt ℝ φ y' ∧ DifferentiableAt ℝ V y' := by
      filter_upwards [hφ.eventually (by simp), hV.eventually (by simp)] with y' h1 h2
      exact ⟨h1.differentiableAt (by norm_num), h2.differentiableAt (by norm_num)⟩
    have heq : (fun y' => fderiv ℝ (fun y' => φ y' • V y') y' (coordinateVector j)) =ᶠ[nhds y]
        fun y' => fderiv ℝ φ y' (coordinateVector j) • V y' +
          φ y' • fderiv ℝ V y' (coordinateVector j) := by
      filter_upwards [hev] with y' ⟨h1, h2⟩
      have h : HasFDerivAt (fun y' => φ y' • V y') _ y' := h1.hasFDerivAt.smul h2.hasFDerivAt
      rw [h.fderiv]
      simp [add_comm]
    rw [heq.fderiv_eq]
    have hA := tcle_diff_fderiv_apply hφ (coordinateVector j)
    have hD := tcle_diff_fderiv_apply hV (coordinateVector j)
    have h1 : HasFDerivAt (fun y' => fderiv ℝ φ y' (coordinateVector j) • V y') _ y :=
      hA.hasFDerivAt.smul hVd.hasFDerivAt
    have h2 : HasFDerivAt (fun y' => φ y' • fderiv ℝ V y' (coordinateVector j)) _ y :=
      hφd.hasFDerivAt.smul hD.hasFDerivAt
    rw [(h1.fun_add h2).fderiv]
    simp
    module
  unfold physLap
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.smul_sum,
    ← Finset.smul_sum]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
