import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem pdComm : UnforcedLeray.Short.IIb.PdComm := by
  intro f j k hf
  funext x
  have hC1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x := (hC1.differentiable (by norm_num)) x
  have hsymm : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  have key : ∀ v w : B0579.Plane,
      fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    intro v w
    have hA : HasFDerivAt (fun y => fderiv ℝ f y v)
        ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hd.hasFDerivAt
    rw [hA.fderiv]
    simp
  have hpd : ∀ i : Fin 2, B0579.pd i f = fun y => fderiv ℝ f y (B0579.dir i) := fun i => rfl
  show fderiv ℝ (B0579.pd k f) x (B0579.dir j) = fderiv ℝ (B0579.pd j f) x (B0579.dir k)
  rw [hpd k, hpd j, key, key]
  exact hsymm.eq _ _

end UnforcedLeray.Short.IIb
