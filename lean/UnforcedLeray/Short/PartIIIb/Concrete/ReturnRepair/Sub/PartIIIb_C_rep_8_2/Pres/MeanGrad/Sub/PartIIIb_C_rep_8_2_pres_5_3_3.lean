import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3_2

/-!
# `TrPd2`: second-order physical derivative of the transported field (`PartIII-b:C/rep/8/2/pres/5/3/3`)

Source of record: `shorter-proof-2026-11-02.tex` lines 4784, 5455, 5267-5268.
With `F = toLp ∘ G ∘ ofLp`, `physPd F l y' = toLp (G' (ofLp y'))` where
`G' v = DG(v) e_l` (`e_l = ofLp (coordinateVector l)`, `‖e_l‖ ≤ 1`). Then `G'` is differentiable
with `DG'(v) = (u ↦ D²G(v)(u)(e_l))`, so `‖DG'(v)‖ ≤ ‖D²G(v)‖`, and `trPd` applied to `G'`
gives the bound.
-/

set_option autoImplicit false

noncomputable section

open WithLp

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeanScaleSub

theorem trPd2 : MeanScaleSub.TrPd2 := by
  unfold MeanScaleSub.TrPd2
  intro G j l y hG
  let L : Space →L[ℝ] Vec3 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
  let R : Vec3 →L[ℝ] Space :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  -- the unit vector e_l in the sup-norm chart
  have hc : ‖(coordinateVector l : Space)‖ = 1 := by
    simp [coordinateVector]
  have he1 : ‖ofLp (coordinateVector l : Space)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have h := PiLp.norm_apply_le (coordinateVector l : Space) i
    rw [hc] at h
    exact h
  -- derivative of `DG` (one derivative of `G` is `C¹`)
  have hG2 : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hDG : ∀ x : Vec3, HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x := fun x =>
    (hG2.differentiable (by norm_num) x).hasFDerivAt
  -- `G' v = DG(v) e_l`
  let Φ : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 := ContinuousLinearMap.apply ℝ Vec3 (ofLp (coordinateVector l : Space))
  let G' : Vec3 → Vec3 := fun v => Φ (fderiv ℝ G v)
  have hG'd : ∀ x : Vec3, HasFDerivAt G' (Φ.comp (fderiv ℝ (fderiv ℝ G) x)) x := fun x =>
    Φ.hasFDerivAt.comp x (hDG x)
  have hG'diff : Differentiable ℝ G' := fun x => (hG'd x).differentiableAt
  -- first derivative of the transported field
  have hF : ∀ z : Space, HasFDerivAt (fun w : Space => toLp 2 (G (ofLp w)))
      (R.comp ((fderiv ℝ G (ofLp z)).comp L)) z := by
    intro z
    have hG' : HasFDerivAt G (fderiv ℝ G (ofLp z)) (L z) :=
      (hG.differentiable (by norm_num) (ofLp z)).hasFDerivAt
    exact R.hasFDerivAt.comp z (hG'.comp z L.hasFDerivAt)
  have hfun : (fun y' : Space => physPd (fun w : Space => toLp 2 (G (ofLp w))) l y') =
      fun y' : Space => toLp 2 (G' (ofLp y')) := by
    funext y'
    unfold physPd
    rw [(hF y').fderiv]
    rfl
  -- the transported `G'`, then the bound of `trPd`
  have h1 : ‖physPd (fun y' : Space => toLp 2 (G' (ofLp y'))) j y‖ ≤
      2 * ‖fderiv ℝ G' (ofLp y)‖ := trPd G' j y hG'diff
  have h2 : ‖fderiv ℝ G' (ofLp y)‖ ≤ ‖fderiv ℝ (fderiv ℝ G) (ofLp y)‖ := by
    rw [(hG'd (ofLp y)).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (fderiv ℝ (fderiv ℝ G) (ofLp y))) fun u => ?_
    calc ‖(Φ.comp (fderiv ℝ (fderiv ℝ G) (ofLp y))) u‖
        = ‖fderiv ℝ (fderiv ℝ G) (ofLp y) u (ofLp (coordinateVector l : Space))‖ := rfl
      _ ≤ ‖fderiv ℝ (fderiv ℝ G) (ofLp y) u‖ * ‖ofLp (coordinateVector l : Space)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ G) (ofLp y)‖ * ‖u‖) * 1 :=
          mul_le_mul (ContinuousLinearMap.le_opNorm _ _) he1 (norm_nonneg _)
            (by positivity)
      _ = ‖fderiv ℝ (fderiv ℝ G) (ofLp y)‖ * ‖u‖ := mul_one _
  unfold physPd2
  rw [hfun]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))

end UnforcedLeray.Short.PartIIIb.Concrete
