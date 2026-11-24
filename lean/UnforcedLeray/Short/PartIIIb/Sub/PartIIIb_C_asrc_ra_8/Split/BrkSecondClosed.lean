import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.BrkFDerivClosed

/-!
# (L3) the second `x`-derivative of the bracket

Source of record: `the November 2 reference manuscript` (73 pages), 4963, 4971-4973,
4978.  `Db_j[w] = G(x_j)·bkD1(x_j, w)` (`brkFDerivClosed`), the Gaussian product rule
`bkG_smul_fderiv`, and the quartic expansion of `bkD1(·, w)` along a line.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bk_bkD1_differentiable (M : Mat3) (a : ℝ) (w : ℝ × ℝ) :
    Differentiable ℝ (fun y => bkD1 M a y w) := by
  unfold bkD1 bkPd bkP bkDot merApply Jrot
  fun_prop

theorem bk_fderiv_bkD1 (M : Mat3) (a : ℝ) (y w u : ℝ × ℝ) :
    fderiv ℝ (fun y' => bkD1 M a y' w) y u =
      bkPdd M a y u w - (bkDot u w / (2 * a)) • bkP M a y - (bkDot y w / (2 * a)) • bkPd M a y u := by
  apply bk_fderiv_of_quartic _ _ _ (bk_bkD1_differentiable M a w y) (bkD1 M a y w) _
    ((((bkDot w (merApply M u) + bkDot u (merApply M w)) / (2 * a)) • Jrot u
        + (bkDot u (merApply M u) / (2 * a)) • Jrot w)
      - ((bkDot y w / (2 * a)) • ((bkDot u (merApply M u) / (2 * a)) • Jrot y
          + ((bkDot u (merApply M y) + bkDot y (merApply M u)) / (2 * a)) • Jrot u)
        + (bkDot u w / (2 * a)) • bkPd M a y u))
    (-((bkDot y w / (2 * a)) • ((bkDot u (merApply M u) / (2 * a)) • Jrot u)
        + (bkDot u w / (2 * a)) • ((bkDot u (merApply M u) / (2 * a)) • Jrot y
          + ((bkDot u (merApply M y) + bkDot y (merApply M u)) / (2 * a)) • Jrot u)))
    (-((bkDot u w / (2 * a)) • ((bkDot u (merApply M u) / (2 * a)) • Jrot u)))
  intro t
  obtain ⟨y1, y2⟩ := y
  obtain ⟨w1, w2⟩ := w
  obtain ⟨u1, u2⟩ := u
  ext <;> simp [bkD1, bkPd, bkPdd, bkP, bkDot, merApply, Jrot] <;> ring

/-- **(L3)** Second `x`-derivative of the bracket (source 4973, 4978; needed for `Δb_j`). -/
theorem brkSecondClosed : BrkSecondClosed := by
  intro ν χ A s j ha w
  have hfun : (fun z => fderiv ℝ (brk ν χ A s j) z w) = fun z =>
      bkG (ageA ν s) (xj ν j z) • bkD1 (Ay ν χ A s) (ageA ν s) (xj ν j z) w :=
    funext fun z => (brkFDerivClosed ν χ A s j ha).2 z w
  have hP := bk_bkD1_differentiable (Ay ν χ A s) (ageA ν s) w
  refine ⟨?_, ?_⟩
  · rw [hfun]
    intro x
    exact (bkG_smul_fderiv ν s j _ hP x 0).1
  · intro x u
    rw [hfun, (bkG_smul_fderiv ν s j _ hP x u).2, bk_fderiv_bkD1]
    rfl

end UnforcedLeray.Short.PartIIIb.Concrete
