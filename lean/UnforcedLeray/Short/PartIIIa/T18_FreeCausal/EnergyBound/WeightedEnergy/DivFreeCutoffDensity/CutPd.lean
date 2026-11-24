import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/9`: product-rule formulas for the cut-off field

Target (`Sub/T18_3_1_1.lean`): `DfcCutPd`. Source of record:
`the November 2 reference manuscript`, lines 3541-3552 as cited by the task
(note: those lines carry the causality/uniqueness paragraph; the cut-off formulas themselves are
the ones stated in the docstring of `DfcCutPd` and of `Sub/T18_3_1_1.lean`, which this file proves).

## Mathematics

Write `dfcCut u k φ θ y = (u_k(y.2) φ₀(y) + u_k'(y.2) θ(y), u_k(y.2) φ₁(y))`, `x = (q, η)`.

* Helper `pdSndMul`: for `ψ : ℝ → ℝ` and `g : ℝ × ℝ → ℝ` differentiable,
  `∂_j (y ↦ ψ(y.2) g(y)) x = ψ(x.2) ∂_j g(x) + g(x) (ψ'(x.2) · (dir j).2)`.
  This is the product rule with `y ↦ ψ(y.2)` whose derivative is `ψ'(x.2) · snd`; since
  `(dir 0).2 = 0` and `(dir 1).2 = 1`, the `∂_q` case has no `ψ'` term and the `∂_η` case has one.
* Helper `pdAddAux`: `∂_j (f + g) = ∂_j f + ∂_j g` at a point where `f, g` are differentiable.
* Main proof: the two components of `dfcCut u k φ θ` are rewritten as the sums
  `u_k(η) φ₀ + u_k'(η) θ` and `u_k(η) φ₁` (by `rfl`), then the helpers give the four formulas.
  Derivatives of `u_k` and `u_k'` are differentiable because `u_k` is smooth
  (`contDiff_infty_iff_deriv`). The second derivative `u_k''` enters only as the value of
  `deriv (deriv (u k))` in the `∂_η` formula for the first component.

The four formulas hold with `u k x.2`, `deriv (u k) x.2`, `deriv (deriv (u k)) x.2` evaluated at
`x.2`; they do not depend on `q` beyond `φ` and `θ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace DfcCutPdAux

/-- The derivative of `y ↦ ψ(y.2)`: it is `ψ'(x.2)` times the second projection. -/
theorem hasFDerivAt_sndComp (ψ : ℝ → ℝ) (hψ : Differentiable ℝ ψ) (x : ℝ × ℝ) :
    HasFDerivAt (fun y : ℝ × ℝ => ψ y.2) (deriv ψ x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
  (hψ x.2).hasDerivAt.comp_hasFDerivAt x
    (hasFDerivAt_snd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) x)

/-- Product rule for the partial derivative `∂_j` of `y ↦ ψ(y.2) g(y)`. -/
theorem pdSndMul (j : Fin 2) (ψ : ℝ → ℝ) (g : ℝ × ℝ → ℝ) (hψ : Differentiable ℝ ψ)
    (hg : Differentiable ℝ g) (x : ℝ × ℝ) :
    B0579.pd j (fun y => ψ y.2 * g y) x =
      ψ x.2 * B0579.pd j g x + g x * (deriv ψ x.2 * (B0579.dir j).2) := by
  have hF : HasFDerivAt (fun y : ℝ × ℝ => ψ y.2 * g y)
      (ψ x.2 • fderiv ℝ g x + g x • (deriv ψ x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    (hasFDerivAt_sndComp ψ hψ x).mul (hg x).hasFDerivAt
  unfold B0579.pd
  rw [hF.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rfl

/-- Additivity of `∂_j` at a point where both summands are differentiable. -/
theorem pdAddAux (j : Fin 2) (f g : ℝ × ℝ → ℝ) (x : ℝ × ℝ) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    B0579.pd j (fun y => f y + g y) x = B0579.pd j f x + B0579.pd j g x := by
  unfold B0579.pd
  rw [fderiv_fun_add hf hg, add_apply]

theorem dir0_snd : (B0579.dir 0).2 = 0 := by simp [B0579.dir]

theorem dir1_snd : (B0579.dir 1).2 = 1 := by simp [B0579.dir]

end DfcCutPdAux

/-- **Product-rule formulas for the cut-off field** (`PartIII-a:T18/3/1/1/9`). Proves `DfcCutPd`:
for smooth `u_k`, smooth `φ` (componentwise) and smooth `θ`, the four partial derivatives of
`dfcCut u k φ θ` are given by the product-rule formulas stated in `DfcCutPd`. -/
theorem dfcCutPd : UnforcedLeray.Short.IIIa.DfcCutPd := by
  unfold UnforcedLeray.Short.IIIa.DfcCutPd
  intro u hu φ θ hφ hθ k x
  have hθd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have hφ0 : Differentiable ℝ (fun y => φ y 0) := (hφ 0).differentiable (by simp)
  have hφ1 : Differentiable ℝ (fun y => φ y 1) := (hφ 1).differentiable (by simp)
  have hud : Differentiable ℝ (u k) := (hu k).differentiable (by simp)
  have hdu : Differentiable ℝ (deriv (u k)) :=
    ((contDiff_infty_iff_deriv.mp (hu k)).2).differentiable (by simp)
  -- the two components of the cut-off field
  have c0 : ∀ y : ℝ × ℝ, dfcCut u k φ θ y 0 = u k y.2 * φ y 0 + deriv (u k) y.2 * θ y :=
    fun y => rfl
  have c1 : ∀ y : ℝ × ℝ, dfcCut u k φ θ y 1 = u k y.2 * φ y 1 := fun y => rfl
  simp only [c0, c1]
  -- differentiability of the summands at `x`
  have dA : DifferentiableAt ℝ (fun y : ℝ × ℝ => u k y.2 * φ y 0) x :=
    ((hud.comp differentiable_snd).mul hφ0).differentiableAt
  have dB : DifferentiableAt ℝ (fun y : ℝ × ℝ => deriv (u k) y.2 * θ y) x :=
    ((hdu.comp differentiable_snd).mul hθd).differentiableAt
  have e0 := DfcCutPdAux.dir0_snd
  have e1 := DfcCutPdAux.dir1_snd
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `∂_q` of the first component
    rw [DfcCutPdAux.pdAddAux 0 _ _ x dA dB, DfcCutPdAux.pdSndMul 0 (u k) _ hud hφ0 x,
      DfcCutPdAux.pdSndMul 0 (deriv (u k)) _ hdu hθd x, e0]
    ring
  · -- `∂_η` of the first component
    rw [DfcCutPdAux.pdAddAux 1 _ _ x dA dB, DfcCutPdAux.pdSndMul 1 (u k) _ hud hφ0 x,
      DfcCutPdAux.pdSndMul 1 (deriv (u k)) _ hdu hθd x, e1]
    ring
  · -- `∂_q` of the second component
    rw [DfcCutPdAux.pdSndMul 0 (u k) _ hud hφ1 x, e0]
    ring
  · -- `∂_η` of the second component
    rw [DfcCutPdAux.pdSndMul 1 (u k) _ hud hφ1 x, e1]
    ring

end UnforcedLeray.Short.IIIa
