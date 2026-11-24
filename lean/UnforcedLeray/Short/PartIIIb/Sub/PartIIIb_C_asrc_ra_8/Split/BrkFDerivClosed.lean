import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.Of

/-!
# `PartIII-b:C/asrc/ra/8/1/1` : (L2) the first `x`-derivative of the bracket

Source of record: `the November 2 reference manuscript` (73 pages), 4963, 4971-4973,
4978.  `b_j = G(x_j)·bkP(x_j)` (`brkClosed`), the Gaussian product rule `bkG_smul_fderiv`, and the
cubic expansion of `bkP` along a line (`bk_fderiv_of_cubic`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bk_bkP_differentiable (M : Mat3) (a : ℝ) : Differentiable ℝ (bkP M a) := by
  unfold bkP bkDot merApply Jrot
  fun_prop

theorem bk_fderiv_bkP (M : Mat3) (a : ℝ) (y w : ℝ × ℝ) :
    fderiv ℝ (bkP M a) y w = bkPd M a y w := by
  apply bk_fderiv_of_cubic _ _ _ (bk_bkP_differentiable M a y) (bkP M a y) (bkPd M a y w)
    ((bkDot w (merApply M w) / (2 * a)) • Jrot y
      + ((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot w)
    ((bkDot w (merApply M w) / (2 * a)) • Jrot w)
  intro t
  obtain ⟨y1, y2⟩ := y
  obtain ⟨w1, w2⟩ := w
  ext <;> simp [bkP, bkPd, bkDot, merApply, Jrot] <;> ring

/-- **(L2)** First `x`-derivative of the bracket (source 4973, 4978). -/
theorem brkFDerivClosed : BrkFDerivClosed := by
  intro ν χ A s j _
  have hfun : brk ν χ A s j = fun z =>
      bkG (ageA ν s) (xj ν j z) • bkP (Ay ν χ A s) (ageA ν s) (xj ν j z) :=
    funext (brkClosed ν χ A s j)
  have hP := bk_bkP_differentiable (Ay ν χ A s) (ageA ν s)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    intro x
    exact (bkG_smul_fderiv ν s j _ hP x 0).1
  · intro x w
    rw [hfun, (bkG_smul_fderiv ν s j _ hP x w).2, bk_fderiv_bkP]
    rfl

end UnforcedLeray.Short.PartIIIb.Concrete
