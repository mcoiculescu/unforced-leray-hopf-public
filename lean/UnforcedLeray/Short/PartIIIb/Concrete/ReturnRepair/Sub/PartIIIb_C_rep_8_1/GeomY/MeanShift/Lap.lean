import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift.Kernel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_org

/-!
# The vector Laplacian through the Hessian trace, and its scaling (source 5383-5387)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fderiv_apply_comp {f : Vec3 → Vec3} {y : Vec3} (hf : DifferentiableAt ℝ f y) (v : Vec3)
    (i : Fin 3) : fderiv ℝ f y v i = fderiv ℝ (fun z => f z i) y v := by
  have := (hasFDerivAt_pi'.1 hf.hasFDerivAt i).fderiv
  rw [this]
  rfl

/-- The vector Laplacian of a smooth field, componentwise, through the Hessian trace. -/
theorem vecLap_apply {X : Vec3 → Vec3} {U : Set Vec3} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {y : Vec3} (hy : y ∈ U) (i : Fin 3) :
    vecLap X y i = ∑ l : Fin 3, iteratedFDeriv ℝ 2 (fun z => X z i) y
      ![Pi.single l 1, Pi.single l 1] := by
  have hXd : ∀ z ∈ U, DifferentiableAt ℝ X z := fun z hz =>
    ((hX.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
  have hXi : ∀ z ∈ U, ContDiffAt ℝ 2 (fun w => X w i) z := fun z hz => by
    have h2 : ContDiffAt ℝ 2 X z := (hX.contDiffAt (hU.mem_nhds hz)).of_le (by norm_cast)
    exact (contDiffAt_pi.1 h2) i
  unfold vecLap
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hg : DifferentiableAt ℝ (fun y' => fderiv ℝ X y' (Pi.single l 1)) y := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ X) y :=
      ((hX.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num))
    exact (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  rw [fderiv_apply_comp hg]
  have hev : (fun y' => fderiv ℝ X y' (Pi.single l 1) i) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ (fun z => X z i) y' (Pi.single l 1) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact fderiv_apply_comp (hXd z hz) _ i
  rw [hev.fderiv_eq, iter2_diag (hXi y hy) l]


/-- Scaling of the Hessian trace under `z ↦ ε z`. -/
theorem trace_scale {h : Vec3 → ℝ} {U : Set Vec3} (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U)
    {ε : ℝ} {y : Vec3} (hy : ε • y ∈ U) :
    ∑ l : Fin 3, iteratedFDeriv ℝ 2 (fun z => h (ε • z)) y ![Pi.single l 1, Pi.single l 1] =
      ε ^ 2 * ∑ l : Fin 3, iteratedFDeriv ℝ 2 h (ε • y) ![Pi.single l 1, Pi.single l 1] := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hc2 : ∀ w ∈ U, ContDiffAt ℝ 2 h w := fun w hw =>
    (hh.contDiffAt (hU.mem_nhds hw)).of_le (by norm_cast)
  have hcomp : ContDiffAt ℝ 2 (fun z => h (ε • z)) y :=
    (hc2 _ hy).comp y (contDiff_const_smul ε).contDiffAt
  rw [iter2_diag hcomp l, iter2_diag (hc2 _ hy) l]
  set e : Vec3 := Pi.single l 1 with he
  have hdiff : ∀ w ∈ U, DifferentiableAt ℝ h w := fun w hw => (hc2 w hw).differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ (fun w => fderiv ℝ h w e) (ε • y) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ h) (ε • y) :=
      ((hh.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num))
    exact (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  have hev : (fun y' => fderiv ℝ (fun z => h (ε • z)) y' e) =ᶠ[𝓝 y]
      fun y' => ε * fderiv ℝ h (ε • y') e := by
    have hcont : ContinuousAt (fun y' : Vec3 => ε • y') y := (continuous_const_smul ε).continuousAt
    filter_upwards [hcont.preimage_mem_nhds (hU.mem_nhds hy)] with z hz
    have hd : DifferentiableAt ℝ h (ε • z) := hdiff _ hz
    have hh2 : HasFDerivAt (fun z' : Vec3 => h (ε • z'))
        ((fderiv ℝ h (ε • z)).comp (ε • ContinuousLinearMap.id ℝ Vec3)) z :=
      hd.hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul ε)
    rw [hh2.fderiv]
    simp
  rw [hev.fderiv_eq]
  have hg3 : HasFDerivAt (fun y' : Vec3 => fderiv ℝ h (ε • y') e)
      ((fderiv ℝ (fun w => fderiv ℝ h w e) (ε • y)).comp (ε • ContinuousLinearMap.id ℝ Vec3)) y :=
    hgd.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul ε)
  rw [(hg3.const_mul ε).fderiv]
  simp
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
