import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Defs

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : the derivative of the bracket `b_j`

Source `the November 2 reference manuscript`
4971-4972: `b_j = B_mer V_j - DV_j(B_mer x_j)` with `D x_j = I`, so
`Db_j(x)v = B_mer(DV_j(x)v) - (D²V_j(x)[v][B_mer x_j] + DV_j(x)(B_mer v))`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rc_xj_hasFDerivAt (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    HasFDerivAt (xj ν j) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := by
  have e : xj ν j = fun y : ℝ × ℝ => y - ((j : ℝ) * cOf ν, (0 : ℝ)) := by
    funext y
    ext <;> simp [xj]
  rw [e]
  exact (hasFDerivAt_id x).sub_const _

theorem rc_brk_hasFDerivAt (ν s : ℝ) (B : Mat3) (j : ℤ) (x : ℝ × ℝ) :
    HasFDerivAt (rcBrk ν s B j)
      ((rcMerL B).comp (fderiv ℝ (Vj ν s j) x) -
        ((fderiv ℝ (Vj ν s j) x).comp ((rcMerL B).comp (ContinuousLinearMap.id ℝ (ℝ × ℝ))) +
          (fderiv ℝ (fderiv ℝ (Vj ν s j)) x).flip (rcMerL B (xj ν j x)))) x := by
  have hV := rc_Vj_contDiff ν s j
  have hV1 : HasFDerivAt (Vj ν s j) (fderiv ℝ (Vj ν s j) x) x :=
    (hV.differentiable (by simp) x).hasFDerivAt
  have hD : HasFDerivAt (fderiv ℝ (Vj ν s j)) (fderiv ℝ (fderiv ℝ (Vj ν s j)) x) x :=
    (((hV.fderiv_right (m := 1) (by simp)).differentiable (by simp)) x).hasFDerivAt
  have h1 : HasFDerivAt (fun y => rcMerL B (Vj ν s j y))
      ((rcMerL B).comp (fderiv ℝ (Vj ν s j) x)) x :=
    (rcMerL B).hasFDerivAt.comp x hV1
  have hu : HasFDerivAt (fun y => rcMerL B (xj ν j y))
      ((rcMerL B).comp (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (rcMerL B).hasFDerivAt.comp x (rc_xj_hasFDerivAt ν j x)
  have h2 := hD.clm_apply hu
  exact h1.sub h2

theorem rc_brk_fderiv (ν s : ℝ) (B : Mat3) (j : ℤ) (x v : ℝ × ℝ) :
    fderiv ℝ (rcBrk ν s B j) x v =
      merApply B (fderiv ℝ (Vj ν s j) x v) -
        (fderiv ℝ (Vj ν s j) x (merApply B v) +
          fderiv ℝ (fderiv ℝ (Vj ν s j)) x v (merApply B (xj ν j x))) := by
  rw [(rc_brk_hasFDerivAt ν s B j x).fderiv]
  simp [rcMerL_apply]

end UnforcedLeray.Short.PartIIIb.Concrete
