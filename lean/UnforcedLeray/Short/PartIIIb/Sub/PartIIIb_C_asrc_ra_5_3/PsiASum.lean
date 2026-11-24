import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_3

/-!
# `PartIII-b:C/asrc/ra/5/3/1` : the lattice-sum form `PsiASum` (source 4963-4968, 4974)

`p_j(s, x) = p_0(s, x_j)` and `∇p_j(x) = ∇p_0(x_j)`, since `x_j = (q - jc, η)` is a
translation with identity derivative and `x_0 = x`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `x_0 = x`. -/
lemma psi_xj_zero (ν : ℝ) (y : ℝ × ℝ) : xj ν 0 y = y := by
  simp [xj]

/-- `p_j = p_0 ∘ x_j`. -/
lemma psi_pj_comp (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) : pj ν s j x = pj ν s 0 (xj ν j x) := by
  simp only [pj, psi_xj_zero]

/-- `∇p_j(x) = ∇p_0(x_j)`. -/
lemma psi_mgrad_shift (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    mgrad (pj ν s j) x = mgrad (pj ν s 0) (xj ν j x) := by
  unfold mgrad
  have hfun : pj ν s j = pj ν s 0 ∘ xj ν j := funext fun y => psi_pj_comp ν s j y
  have hg : HasFDerivAt (xj ν j) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := by
    have e : xj ν j = fun y : ℝ × ℝ => y - ((j : ℝ) * cOf ν, 0) := by
      funext y
      ext <;> simp [xj]
    rw [e]
    exact (hasFDerivAt_id x).sub_const _
  have hf : HasFDerivAt (pj ν s 0) (fderiv ℝ (pj ν s 0) (xj ν j x)) (xj ν j x) := by
    have hd : DifferentiableAt ℝ (pj ν s 0) (xj ν j x) := by
      unfold pj xj sq2
      fun_prop
    exact hd.hasFDerivAt
  have hc := HasFDerivAt.comp x hf hg
  rw [hfun, hc.fderiv, ContinuousLinearMap.comp_id]

/-- (N3) lattice-sum form of `PsiA`. -/
theorem psiASum_proof : PsiASum := by
  intro ν χ A
  funext p
  show PsiA ν χ A p.1 p.2 = ∑' j : ℤ, GpsiA ν χ A (p.1, (p.2.1 - j * cOf ν, p.2.2))
  unfold PsiA GpsiA
  apply tsum_congr
  intro j
  rw [psi_mgrad_shift]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
