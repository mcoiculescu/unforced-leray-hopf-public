import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `C/inst/5` helper: the `ψ^p_A` lattice terms are translates of one function (source 4973-4980)

For fixed `ν, s > 0` and a fixed matrix `M = A^y(s)`, the `j`-th term of `ψ^p_A` at `x` equals
`Φ(x_j)` with `x_j = (q - jc, η)` and `Φ` independent of `j`:
`Φ(y) = -2a⁻¹ e^{-|y|²/(4a)} (tr M - c₁(y, My))`, where `c₁(y,v) = -(2y·v)/(4a)` (the derivative
coefficient of `ψ_j` along `v`, `gp_fderiv_psij`).  Hence `ψ^p_A(s, x) = Σ_j Φ(x_j)`.
This is the algebraic reduction used by the x-part and the s-part of `PsipADiff`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The fixed profile `Φ` with `ψ^p_A` terms `Φ(x_j)` (source 4973-4975). -/
def psiPhi (ν s : ℝ) (M : Mat3) (y : ℝ × ℝ) : ℝ :=
  (-2 * (ageA ν s)⁻¹) * Real.exp (-(sq2 y) / (4 * ageA ν s)) *
    (merTrace M - (-(2 * y.1 * (merApply M y).1 + 2 * y.2 * (merApply M y).2) / (4 * ageA ν s)))

/-- The `j`-th term of `ψ^p_A` is the translate `Φ(x_j)`. -/
theorem psipATerm_eq_phi (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ)
    (ha : 0 < ageA ν s) :
    psipATerm ν χ A s x j = psiPhi ν s (Ay ν χ A s) (xj ν j x) := by
  unfold psipATerm psiPhi
  rw [gp_fderiv_psij]
  unfold psij
  ring

/-- `ψ^p_A` is the sum of the translates `Φ(x_j)`. -/
theorem psipA_eq_phi (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (ha : 0 < ageA ν s) :
    psipA ν χ A s x = ∑' j : ℤ, psiPhi ν s (Ay ν χ A s) (xj ν j x) := by
  rw [psipA_eq]
  exact tsum_congr fun j => psipATerm_eq_phi ν χ A s x j ha

end UnforcedLeray.Short.PartIIIb.Concrete
