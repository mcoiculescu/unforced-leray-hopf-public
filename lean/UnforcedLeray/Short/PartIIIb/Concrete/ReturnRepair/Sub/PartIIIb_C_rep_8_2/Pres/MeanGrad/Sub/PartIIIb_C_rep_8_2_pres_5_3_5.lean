import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3

/-!
# `ScD2`: second derivative of the scaled field (`PartIII-b:C/rep/8/2/pres/5/3/5`)

Source of record: `shorter-proof-2026-11-02.tex` lines 4784, 5455, 5267-5268.
`D(D(ε²X(ε·)))(v) = (ε³)·ε·D²X(εv)∘(composition with ε·id)`, so the operator norm is at most
`ε⁴ ‖D²X(εv)‖ = ε⁴ ‖iteratedFDeriv 2 X (εv)‖`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeanScaleSub

theorem scD2 : MeanScaleSub.ScD2 := by
  unfold MeanScaleSub.ScD2
  intro X ε v hX hε
  have h1 : HasFDerivAt (fun y' : Vec3 => ε • y') (ε • ContinuousLinearMap.id ℝ Vec3) v :=
    (hasFDerivAt_id v).const_smul ε
  have h2 : HasFDerivAt (fun y' : Vec3 => fderiv ℝ X (ε • y'))
      ((fderiv ℝ (fderiv ℝ X) (ε • v)).comp (ε • ContinuousLinearMap.id ℝ Vec3)) v :=
    (JetClockCore.dX_hasFDeriv hX (ε • v)).comp v h1
  have h3 : HasFDerivAt (fun y' : Vec3 => (ε ^ 2 * ε) • fderiv ℝ X (ε • y'))
      ((ε ^ 2 * ε) • ((fderiv ℝ (fderiv ℝ X) (ε • v)).comp (ε • ContinuousLinearMap.id ℝ Vec3))) v :=
    h2.const_smul (ε ^ 2 * ε)
  have e : fderiv ℝ (JetClockCore.Xsc X ε) = fun y' : Vec3 => (ε ^ 2 * ε) • fderiv ℝ X (ε • y') :=
    funext fun y' => JetClockCore.fderiv_Xsc hX ε y'
  have hnorm2 : ‖fderiv ℝ (fderiv ℝ X) (ε • v)‖ = ‖iteratedFDeriv ℝ 2 X (ε • v)‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  have hid : ‖ε • ContinuousLinearMap.id ℝ Vec3‖ ≤ ε := by
    refine (norm_smul_le ε (ContinuousLinearMap.id ℝ Vec3)).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos hε]
    exact mul_le_of_le_one_right hε.le ContinuousLinearMap.norm_id_le
  have hop : ‖(fderiv ℝ (fderiv ℝ X) (ε • v)).comp (ε • ContinuousLinearMap.id ℝ Vec3)‖ ≤
      ‖fderiv ℝ (fderiv ℝ X) (ε • v)‖ * ε :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left hid (norm_nonneg _))
  have hc : (0 : ℝ) ≤ ε ^ 2 * ε := by positivity
  rw [e, h3.fderiv]
  calc ‖(ε ^ 2 * ε) • (fderiv ℝ (fderiv ℝ X) (ε • v)).comp (ε • ContinuousLinearMap.id ℝ Vec3)‖
      ≤ ‖ε ^ 2 * ε‖ * ‖(fderiv ℝ (fderiv ℝ X) (ε • v)).comp (ε • ContinuousLinearMap.id ℝ Vec3)‖ :=
        ContinuousLinearMap.opNorm_smul_le (ε ^ 2 * ε) _
    _ = (ε ^ 2 * ε) * ‖(fderiv ℝ (fderiv ℝ X) (ε • v)).comp (ε • ContinuousLinearMap.id ℝ Vec3)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ (ε ^ 2 * ε) * (‖fderiv ℝ (fderiv ℝ X) (ε • v)‖ * ε) := mul_le_mul_of_nonneg_left hop hc
    _ = ε ^ 4 * ‖fderiv ℝ (fderiv ℝ X) (ε • v)‖ := by ring
    _ = ε ^ 4 * ‖iteratedFDeriv ℝ 2 X (ε • v)‖ := by rw [hnorm2]

end UnforcedLeray.Short.PartIIIb.Concrete
