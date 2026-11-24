import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- `nzS2` of a smooth function is smooth. -/
theorem nzfpS2Smooth (h : ℝ × ℝ → ℂ) (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (nzS2 h) := by
  unfold nzS2
  have hfd : ContDiff ℝ ∞ (fderiv ℝ h) := hh.fderiv_right (by simp)
  exact contDiff_fst.smul (hfd.clm_apply contDiff_const)

/-- Iterates of `nzS2` of a smooth function are smooth. -/
theorem nzfpS2IterSmooth (α : ℕ) : ∀ h : ℝ × ℝ → ℂ, ContDiff ℝ ∞ h →
    ContDiff ℝ ∞ (nzS2^[α] h) := by
  induction α with
  | zero => intro h hh; exact hh
  | succ n ih =>
    intro h hh
    rw [Function.iterate_succ_apply]
    exact ih (nzS2 h) (nzfpS2Smooth h hh)

/-- `nzS2` commutes with multiplication by `i`. -/
theorem nzfpS2Mul (h : ℝ × ℝ → ℂ) (hh : ContDiff ℝ ∞ h) :
    nzS2 (fun x => Complex.I * h x) = fun x => Complex.I * nzS2 h x := by
  funext x
  have hdiff : DifferentiableAt ℝ h x := (hh.differentiable (by simp)) x
  have hd : HasFDerivAt (fun y => Complex.I * h y) (Complex.I • fderiv ℝ h x) x :=
    hdiff.hasFDerivAt.const_mul Complex.I
  unfold nzS2
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- Iterates of `nzS2` commute with multiplication by `i` on smooth functions. -/
theorem nzfpS2IterMul (α : ℕ) : ∀ h : ℝ × ℝ → ℂ, ContDiff ℝ ∞ h →
    nzS2^[α] (fun x => Complex.I * h x) = fun x => Complex.I * nzS2^[α] h x := by
  induction α with
  | zero => intro h hh; rfl
  | succ n ih =>
    intro h hh
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, nzfpS2Mul h hh]
    exact ih (nzS2 h) (nzfpS2Smooth h hh)

theorem nzFpMomI : UnforcedLeray.Short.PartIIa.NzFpMomI := by
  unfold NzFpMomI
  intro h hh j α
  have key : ∀ x : ℝ × ℝ,
      ‖(nzS2^[α] (fun x => Complex.I * h x)) x‖ = ‖(nzS2^[α] h) x‖ := by
    intro x
    rw [nzfpS2IterMul α h hh]
    simp
  unfold nzMom2
  simp only [key]

end UnforcedLeray.Short.PartIIa
