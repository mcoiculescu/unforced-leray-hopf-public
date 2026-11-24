import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.Of

/-!
# (L5) the second `x`-derivative of the Gaussian `V_j`

Source of record: `the November 2 reference manuscript` (73 pages), 4963, 4971.
`DV_j[w] = G(x_j)·bkV1(x_j, w)` (`bk_Vj_fderiv`), the Gaussian product rule `bkG_smul_fderiv`, and
the quadratic expansion of `bkV1(·, w)` along a line.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bk_bkV1_differentiable (a : ℝ) (w : ℝ × ℝ) : Differentiable ℝ (fun y => bkV1 a y w) := by
  unfold bkV1 bkDot Jrot
  fun_prop

theorem bk_fderiv_bkV1 (a : ℝ) (y w u : ℝ × ℝ) :
    fderiv ℝ (fun y' => bkV1 a y' w) y u =
      -(bkDot u w / (2 * a)) • Jrot y - (bkDot y w / (2 * a)) • Jrot u := by
  apply bk_fderiv_of_cubic _ _ _ (bk_bkV1_differentiable a w y) (bkV1 a y w) _
    (-(bkDot u w / (2 * a)) • Jrot u) 0
  intro t
  obtain ⟨y1, y2⟩ := y
  obtain ⟨w1, w2⟩ := w
  obtain ⟨u1, u2⟩ := u
  ext <;> simp [bkV1, bkDot, Jrot] <;> ring

/-- **(L5)** Second `x`-derivative of the Gaussian `V_j` (source 4963, 4971). -/
theorem vjSecondClosed : VjSecondClosed := by
  intro ν s j _ w
  have hfun : (fun z => fderiv ℝ (Vj ν s j) z w) = fun z =>
      bkG (ageA ν s) (xj ν j z) • bkV1 (ageA ν s) (xj ν j z) w :=
    funext fun z => bk_Vj_fderiv ν s j z w
  have hP := bk_bkV1_differentiable (ageA ν s) w
  refine ⟨?_, ?_⟩
  · rw [hfun]
    intro x
    exact (bkG_smul_fderiv ν s j _ hP x 0).1
  · intro x u
    rw [hfun, (bkG_smul_fderiv ν s j _ hP x u).2, bk_fderiv_bkV1]
    rfl

end UnforcedLeray.Short.PartIIIb.Concrete
