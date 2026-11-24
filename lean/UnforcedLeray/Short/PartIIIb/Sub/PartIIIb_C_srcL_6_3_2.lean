import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_3

/-!
# Smoothness of the dilated family (task `PartIII-b:C/srcL/6/3/2`)

Proves `XSPsiFamSmooth` (see `Sub/PartIII-b_C_srcL_6_3.lean`): for `σ > 1` the map
`y ↦ σ * Z (scaleXY σ y) 2` is `C^∞` on `{b < cylR y ^ 2}`.  The dilation `scaleXY σ` is linear
and maps the region into itself, since `cylR (scaleXY σ y)^2 = σ^2 (y 0^2 + y 1^2) ≥ cylR y^2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem xsPsiFamSmooth : XSPsiFamSmooth := by
  intro b Z hH σ hσ
  obtain ⟨_, hZ, _⟩ := hH
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scaleXY σ) := by
    unfold scaleXY
    rw [contDiff_pi]
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hmaps : MapsTo (scaleXY σ) {y : Vec3 | b < cylR y ^ 2} {y : Vec3 | b < cylR y ^ 2} := by
    intro y hy
    have hy' : b < cylR y ^ 2 := hy
    have hσ1 : (1 : ℝ) ≤ σ ^ 2 := by
      have : (1 : ℝ) ≤ σ := le_of_lt hσ
      nlinarith
    show b < cylR (scaleXY σ y) ^ 2
    rw [cylR_sq] at hy' ⊢
    unfold scaleXY
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hnn : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
    nlinarith [mul_nonneg hnn (sub_nonneg.mpr hσ1)]
  have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Z ∘ scaleXY σ) {y : Vec3 | b < cylR y ^ 2} :=
    hZ.comp hlin.contDiffOn hmaps
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Vec3 => (Z ∘ scaleXY σ) y 2) {y : Vec3 | b < cylR y ^ 2} :=
    (contDiff_apply ℝ ℝ 2).comp_contDiffOn hcomp
  exact (contDiffOn_const.mul h2)

end UnforcedLeray.Short.PartIIIb.Concrete
