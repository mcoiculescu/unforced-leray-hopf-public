import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.Of

/-!
# (L6) the gradient of the pressure potential `Ψ_j = (A^y_mer x_j)·∇p_j`

Source of record: `the November 2 reference manuscript` (73 pages), 4964, 5024.
`∇p_j = G²x_j` (`bk_mgrad_pj`), so `Ψ_j = G·(G·(x_j·Mx_j))`; two Gaussian product rules
(`bkG_smul_fderiv`) and the quadratic expansion of `y·My` give
`∇Ψ_j = G²((M + Mᵀ)x_j - (x_j·Mx_j)/a · x_j)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The Gaussian product rule at `j = 0` without the lattice shift. -/
theorem bk_bkG_smul_fderiv_plain {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (ν s : ℝ)
    (P : ℝ × ℝ → E) (hP : Differentiable ℝ P) (y u : ℝ × ℝ) :
    DifferentiableAt ℝ (fun z => bkG (ageA ν s) z • P z) y ∧
      fderiv ℝ (fun z => bkG (ageA ν s) z • P z) y u =
        bkG (ageA ν s) y • (fderiv ℝ P y u - (bkDot y u / (2 * ageA ν s)) • P y) := by
  have hx0 : xj ν 0 = fun z => z := by
    funext z
    simp [xj]
  have h := bkG_smul_fderiv ν s 0 P hP y u
  rw [hx0] at h
  exact h

/-- The quadratic form `y ↦ (My)·y`. -/
def bkQf (M : Mat3) (y : ℝ × ℝ) : ℝ := bkDot (merApply M y) y

theorem bk_bkQf_differentiable (M : Mat3) : Differentiable ℝ (bkQf M) := by
  unfold bkQf bkDot merApply
  fun_prop

theorem bk_fderiv_bkQf (M : Mat3) (y u : ℝ × ℝ) :
    fderiv ℝ (bkQf M) y u = bkDot (merApply M u) y + bkDot (merApply M y) u := by
  apply bk_fderiv_of_cubic _ _ _ (bk_bkQf_differentiable M y) (bkQf M y) _
    (bkDot (merApply M u) u) 0
  intro t
  obtain ⟨y1, y2⟩ := y
  obtain ⟨u1, u2⟩ := u
  simp [bkQf, bkDot, merApply]
  ring

/-- The inner profile `G(y)·(My)·y`. -/
def bkPq (ν s : ℝ) (M : Mat3) (y : ℝ × ℝ) : ℝ := bkG (ageA ν s) y • bkQf M y

theorem bk_bkPq_differentiable (ν s : ℝ) (M : Mat3) : Differentiable ℝ (bkPq ν s M) := by
  unfold bkPq bkG bkQf bkDot merApply sq2
  fun_prop

/-- **(L6)** The gradient of `Ψ_j` (source 4964, 5024). -/
theorem mgradPsiAjClosed : MgradPsiAjClosed := by
  intro ν χ A s j ha
  have hfun : PsiAj ν χ A s j = fun z =>
      bkG (ageA ν s) (xj ν j z) • bkPq ν s (Ay ν χ A s) (xj ν j z) := by
    funext z
    unfold PsiAj
    rw [bk_mgrad_pj ν s j z ha]
    simp only [bkPq, bkQf, bkDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hP := bk_bkPq_differentiable ν s (Ay ν χ A s)
  have hQ := bk_bkQf_differentiable (Ay ν χ A s)
  have ha0 : ageA ν s ≠ 0 := ha.ne'
  refine ⟨?_, ?_⟩
  · rw [hfun]
    intro x
    exact (bkG_smul_fderiv ν s j _ hP x 0).1
  · intro x
    have key : ∀ u : ℝ × ℝ, fderiv ℝ (PsiAj ν χ A s j) x u =
        bkG (ageA ν s) (xj ν j x) • (bkG (ageA ν s) (xj ν j x) •
          (fderiv ℝ (bkQf (Ay ν χ A s)) (xj ν j x) u
            - (bkDot (xj ν j x) u / (2 * ageA ν s)) • bkQf (Ay ν χ A s) (xj ν j x))
          - (bkDot (xj ν j x) u / (2 * ageA ν s)) • bkPq ν s (Ay ν χ A s) (xj ν j x)) := by
      intro u
      rw [hfun, (bkG_smul_fderiv ν s j _ hP x u).2]
      have hp : bkPq ν s (Ay ν χ A s) = fun z => bkG (ageA ν s) z • bkQf (Ay ν χ A s) z := rfl
      rw [hp, (bk_bkG_smul_fderiv_plain ν s _ hQ (xj ν j x) u).2]
    unfold mgrad
    rw [key, key, bk_fderiv_bkQf, bk_fderiv_bkQf]
    obtain ⟨y1, y2⟩ := xj ν j x
    simp only [bkPsi, bkPq, bkQf, bkDot, merApply, tr3, ei, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul, Prod.smul_mk]
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul] <;> field_simp <;> ring

end UnforcedLeray.Short.PartIIIb.Concrete
