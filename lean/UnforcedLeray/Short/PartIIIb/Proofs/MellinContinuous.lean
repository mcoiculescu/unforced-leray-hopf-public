import UnforcedLeray.Short.PartIIIb.Tasks
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Proof of `mellinContinuousAt` (target `T_mellinContinuousAt`; source: `the November 2 reference manuscript`, lines 4703 and 5924-5926)

`mellinC lam ell J μ = (63π i/128) · ell · (Γ(μ+5/2) / lam^(μ+5/2)) · J μ` (Scalar.lean).
At a real point `σ₀ > 0` with `Re lam > 0` and `J` continuous at `σ₀`, each factor is continuous:

* `μ ↦ Γ(μ+5/2)` is differentiable at `σ₀+5/2`, since `Re(σ₀+5/2) > 0` excludes the poles `-m`;
* `μ ↦ lam^(μ+5/2)` is continuous because `lam ≠ 0`;
* the denominator `lam^(σ₀+5/2)` is nonzero, so the quotient is continuous at `σ₀`;
* products of functions continuous at `σ₀` are continuous at `σ₀`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

theorem mellinContinuousAt : UnforcedLeray.Short.PartIIIb.T_mellinContinuousAt := by
  intro lam ell J σ₀ hlam hσ hJ
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h] at hlam
    simp at hlam
  -- real part of the argument of Γ and of the power
  have hre : ((σ₀ : ℂ) + 5 / 2).re = σ₀ + 5 / 2 := by
    simp
  -- the argument avoids the poles `-m` of Γ
  have hpole : ∀ m : ℕ, (σ₀ : ℂ) + 5 / 2 ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    rw [hre] at h'
    simp at h'
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hlin : ContinuousAt (fun μ : ℂ => μ + 5 / 2) (σ₀ : ℂ) :=
    continuousAt_id.add continuousAt_const
  have hGam : ContinuousAt Complex.Gamma ((σ₀ : ℂ) + 5 / 2) :=
    (Complex.differentiableAt_Gamma _ hpole).continuousAt
  have hG : ContinuousAt (fun μ : ℂ => Complex.Gamma (μ + 5 / 2)) (σ₀ : ℂ) :=
    ContinuousAt.comp_of_eq hGam hlin rfl
  have hPow : ContinuousAt (fun x : ℂ => lam ^ x) ((σ₀ : ℂ) + 5 / 2) :=
    continuousAt_const_cpow hlam0
  have hP : ContinuousAt (fun μ : ℂ => lam ^ (μ + 5 / 2)) (σ₀ : ℂ) :=
    ContinuousAt.comp_of_eq hPow hlin rfl
  have hPne : lam ^ ((σ₀ : ℂ) + 5 / 2) ≠ 0 := by
    intro h
    exact hlam0 ((Complex.cpow_eq_zero_iff _ _).1 h).1
  have hQ : ContinuousAt (fun μ : ℂ => Complex.Gamma (μ + 5 / 2) / lam ^ (μ + 5 / 2)) (σ₀ : ℂ) :=
    hG.div hP hPne
  have hC : ContinuousAt (fun μ : ℂ =>
      ((63 * Real.pi / 128 : ℝ) : ℂ) * Complex.I * (ell * (Complex.Gamma (μ + 5 / 2) / lam ^ (μ + 5 / 2)))
        * J μ) (σ₀ : ℂ) :=
    (continuousAt_const.mul (continuousAt_const.mul hQ)).mul hJ
  show ContinuousAt (fun μ : ℂ =>
      ((63 * Real.pi / 128 : ℝ) : ℂ) * Complex.I * (ell * (Complex.Gamma (μ + 5 / 2) / lam ^ (μ + 5 / 2)))
        * J μ) (σ₀ : ℂ)
  exact hC

end UnforcedLeray.Short.PartIIIb
