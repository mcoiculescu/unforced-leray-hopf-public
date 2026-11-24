import UnforcedLeray.Units.B0009
import Mathlib.Analysis.Complex.Liouville

/-!
# Part I, task `PartI:S04`: the Biot-Savart velocity is `∇^⊥Ψ` (conditional)

Source of record: `the November 2 reference manuscript`, lines 790-802
(`K q = ∇^⊥Ψ` for the streamfunction `Ψ` with `ΔΨ = q` and `∇Ψ → 0`, hence the velocity is in `L²`).

Route (Liouville on the difference of the two velocity fields). Write `w = (w₀, w₁) = (K₀q, K₁q)`
for the components of `B0009.biotSavart q` and `V = (-∂₂Ψ, ∂₁Ψ)`. Three facts about `w`:

* `BiotSavartDerivFormula`: `w` is `C¹` and `∂_v w = K (∂_v q)` (differentiation under the integral);
* `BiotSavartDivFree`, `BiotSavartCurl`: `div w = 0` and `curl w = ∂₁w₁ - ∂₂w₀ = q`
  (Green identity for the kernel `K = ∇^⊥N`, in polar coordinates around `y`);
* `BiotSavartDecay`: `w → 0` at infinity.

Then `a₀ = w₀ + ∂₂Ψ`, `a₁ = w₁ - ∂₁Ψ` are `C¹`, `div a = curl a = 0`, and tend to `0`, so
`a₁ + i a₀` is entire (`∂₁ + i∂₂ = 0`) and `conj (a₁ - i a₀)` is entire, both bounded and tending to
`0`; Liouville gives `a = 0`. This is the proof of `biotSavart_eq_perpGrad_of`; the unconditional
statement is the task `PartI:S04` (`Short/PartI/Tasks/BiotSavartPerpGrad.lean`).

Sign convention (checked): `B0009.kernel 0 z = -∂₂N(z)`, `B0009.kernel 1 z = ∂₁N(z)` for
`N = (2π)⁻¹ log|z|`, so `K q = (-∂₂, ∂₁)(N ⋆ q) = ∇^⊥ Δ⁻¹ q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- The Gaussian-class hypothesis on a vorticity `q`: smooth with every derivative bounded by
`(1 + |y|)^N e^{-|y|²/4}`. -/
def PlanarGaussianClass (q : ℂ → ℂ) : Prop :=
  ContDiff ℝ ∞ q ∧ ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y,
    ‖iteratedFDeriv ℝ k q y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)

/-- **Differentiation under the integral** (source lines 790-802): for `q` in the Gaussian class
the components `K_i q` of the Biot-Savart velocity are `C¹` and `∂_v (K_i q) = K_i (∂_v q)`.
Proof: `K_i ∈ L¹_loc` with `|K_i(z)| ≤ (2π|z|)⁻¹` (`B0009.norm_kernel_le`,
`B0009.integrableOn_kernel_ball`); write `K_i q (y) = ∫ K_i(t) q(y - t) dt`, differentiate under the
integral with the dominating function `|K_i(t)| sup_{|y - y₀| ≤ 1} |∇q(y - t)|` (integrable by the
Gaussian bounds), and note that the derivative is again of the same form, hence continuous. -/
def BiotSavartDerivFormula : Prop :=
  ∀ {q : ℂ → ℂ}, PlanarGaussianClass q → ∀ i : Fin 2,
    ContDiff ℝ 1 (B0009.biotSavart q i) ∧
      ∀ y v : ℂ, fderiv ℝ (B0009.biotSavart q i) y v =
        B0009.biotSavart (fun z => fderiv ℝ q z v) i y

/-- **`div K q = 0`, in the form `K₀(∂₁q) + K₁(∂₂q) = 0`** (source lines 790-802): the angular
half of the Green identity. Proof: with `t = y - z` and `g(r, ϑ) = q(y - r e^{iϑ})` one has
`(-t₂ ∂₁q + t₁ ∂₂q)(y - t) = -∂_ϑ g`, so
`K₀(∂₁q)(y) + K₁(∂₂q)(y) = -(2π)⁻¹ ∫₀^∞ r⁻¹ ∫₀^{2π} ∂_ϑ g dϑ dr = 0` by periodicity
(polar coordinates: `Complex.integral_comp_polarCoord_symm`; `|∂_ϑ g| ≤ r |∇q|` makes the
integrand integrable near `r = 0`). -/
def BiotSavartDivFree : Prop :=
  ∀ {q : ℂ → ℂ}, PlanarGaussianClass q → ∀ y : ℂ,
    B0009.biotSavart (fun z => fderiv ℝ q z 1) 0 y +
      B0009.biotSavart (fun z => fderiv ℝ q z Complex.I) 1 y = 0

/-- **`curl K q = q`, in the form `K₁(∂₁q) - K₀(∂₂q) = q`** (source lines 790-802): the radial half
of the Green identity (`ΔN = δ`). Proof: with `g(r, ϑ) = q(y - r e^{iϑ})` one has
`(t₁ ∂₁q + t₂ ∂₂q)(y - t) = -r ∂_r g`, so
`K₁(∂₁q)(y) - K₀(∂₂q)(y) = -(2π)⁻¹ ∫₀^{2π} ∫₀^∞ ∂_r g dr dϑ = (2π)⁻¹ ∫₀^{2π} g(0, ϑ) dϑ = q(y)`
(fundamental theorem of calculus in `r`, `g(r, ϑ) → 0` as `r → ∞` by the Gaussian bound). -/
def BiotSavartCurl : Prop :=
  ∀ {q : ℂ → ℂ}, PlanarGaussianClass q → ∀ y : ℂ,
    B0009.biotSavart (fun z => fderiv ℝ q z 1) 1 y -
      B0009.biotSavart (fun z => fderiv ℝ q z Complex.I) 0 y = q y

/-- **Decay of the velocity** (source lines 790-802): `K q (y) → 0` as `|y| → ∞` for `q` in the
Gaussian class. Proof: split the integral `∫ K(y - z) q(z) dz` at `|z| = |y|/2`: on `|z| ≤ |y|/2`
use `|K(y - z)| ≤ (π|y|)⁻¹` (`B0009.norm_kernel_le`) and `q ∈ L¹`; on `|z| > |y|/2` use
`sup_{|z| > |y|/2} |q| → 0` and `∫_{|t| ≤ 1} |K| < ∞` plus `|K| ≤ (2π)⁻¹` off the unit ball
(this is the proof of `B0009.convolutionExistsAt_kernel`). The total mass `∫ q` is not needed. -/
def BiotSavartDecay : Prop :=
  ∀ {q : ℂ → ℂ}, PlanarGaussianClass q → ∀ i : Fin 2,
    Tendsto (B0009.biotSavart q i) (cocompact ℂ) (𝓝 0)

/-! ### Liouville for `∂₁ f + i ∂₂ f = 0` -/

/-- A `C¹` function with `∂₁ f + i ∂₂ f = 0` that tends to `0` at infinity vanishes. -/
theorem eq_zero_of_dbar_eq_zero {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (h : ∀ y, fderiv ℝ f y 1 + Complex.I * fderiv ℝ f y Complex.I = 0)
    (hdec : Tendsto f (cocompact ℂ) (𝓝 0)) : ∀ y, f y = 0 := by
  have hdiff : Differentiable ℂ f := by
    intro y
    have hR : DifferentiableAt ℝ f y := (hf.differentiable one_ne_zero) y
    rw [differentiableAt_iff_restrictScalars ℝ hR]
    refine ⟨ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (fderiv ℝ f y 1), ?_⟩
    have hDI : fderiv ℝ f y Complex.I = Complex.I * fderiv ℝ f y 1 := by
      linear_combination (-Complex.I) * h y + (fderiv ℝ f y Complex.I) * Complex.I_sq
    ext1 z
    have hz : z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I := by
      apply Complex.ext <;> simp
    have e1 : (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (fderiv ℝ f y 1)).restrictScalars ℝ z
        = z * fderiv ℝ f y 1 := by
      simp
    rw [e1]
    conv_rhs => rw [hz]
    rw [map_add, map_smul, map_smul, hDI, Complex.real_smul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im z]
    ring
  intro y
  exact hdiff.apply_eq_of_tendsto_cocompact y hdec

/-! ### Assembly -/

theorem fderiv_fderiv_apply {Ψ : ℂ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (y u v : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ Ψ y u) y v = fderiv ℝ (fderiv ℝ Ψ) y v u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ Ψ) y :=
    ((hΨ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y
  rw [fderiv_clm_apply hd (differentiableAt_const u)]
  simp

theorem tendsto_fderiv_apply {Ψ : ℂ → ℂ}
    (hdec : Tendsto (fderiv ℝ Ψ) (cocompact ℂ) (𝓝 0)) (u : ℂ) :
    Tendsto (fun y => fderiv ℝ Ψ y u) (cocompact ℂ) (𝓝 0) := by
  have h : Tendsto (fun y => fderiv ℝ Ψ y u) (cocompact ℂ)
      (𝓝 ((ContinuousLinearMap.apply ℝ ℂ u) 0)) :=
    ((ContinuousLinearMap.apply ℝ ℂ u).continuous.tendsto 0).comp hdec
  simpa using h

/-- **`K q = ∇^⊥Ψ`** (source lines 790-802), from the four Props above: if `Ψ` is smooth,
`ΔΨ = q` and `∇Ψ → 0` at infinity, with `q` smooth with Gaussian-class derivative bounds, then
`(K₀ q, K₁ q) = (-∂₂Ψ, ∂₁Ψ)`. The hypothesis `∫ q = 0` is not used. -/
theorem biotSavart_eq_perpGrad_of (hD : BiotSavartDerivFormula) (hDiv : BiotSavartDivFree)
    (hCurl : BiotSavartCurl) (hDec : BiotSavartDecay)
    {q Ψ : ℂ → ℂ} (hq : ContDiff ℝ ∞ q)
    (hqb : ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y,
      ‖iteratedFDeriv ℝ k q y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4))
    (hq0 : ∫ y, q y = 0) (hΨ : ContDiff ℝ ∞ Ψ)
    (hlap : ∀ y, iteratedFDeriv ℝ 2 Ψ y ![1, 1] +
      iteratedFDeriv ℝ 2 Ψ y ![Complex.I, Complex.I] = q y)
    (hdec : Tendsto (fderiv ℝ Ψ) (cocompact ℂ) (𝓝 0)) :
    ∀ y, B0009.biotSavart q 0 y = -(fderiv ℝ Ψ y Complex.I) ∧
      B0009.biotSavart q 1 y = fderiv ℝ Ψ y 1 := by
  have hG : PlanarGaussianClass q := ⟨hq, hqb⟩
  obtain ⟨hw0c, hw0d⟩ := hD hG 0
  obtain ⟨hw1c, hw1d⟩ := hD hG 1
  -- smoothness of the components of `∇Ψ`
  have hV : ∀ u : ℂ, ContDiff ℝ ∞ fun y => fderiv ℝ Ψ y u := fun u =>
    (hΨ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hV1 : ∀ u : ℂ, ContDiff ℝ 1 fun y => fderiv ℝ Ψ y u := fun u => (hV u).of_le (by simp)
  -- the residual fields
  set a0 : ℂ → ℂ := fun y => B0009.biotSavart q 0 y + fderiv ℝ Ψ y Complex.I with ha0
  set a1 : ℂ → ℂ := fun y => B0009.biotSavart q 1 y - fderiv ℝ Ψ y 1 with ha1
  have ha0c : ContDiff ℝ 1 a0 := hw0c.add (hV1 _)
  have ha1c : ContDiff ℝ 1 a1 := hw1c.sub (hV1 _)
  have ha0d : ∀ y, DifferentiableAt ℝ a0 y := fun y => (ha0c.differentiable one_ne_zero) y
  have ha1d : ∀ y, DifferentiableAt ℝ a1 y := fun y => (ha1c.differentiable one_ne_zero) y
  have hw0dd : ∀ y, DifferentiableAt ℝ (B0009.biotSavart q 0) y := fun y =>
    (hw0c.differentiable one_ne_zero) y
  have hw1dd : ∀ y, DifferentiableAt ℝ (B0009.biotSavart q 1) y := fun y =>
    (hw1c.differentiable one_ne_zero) y
  have hVd : ∀ (u : ℂ) y, DifferentiableAt ℝ (fun y => fderiv ℝ Ψ y u) y := fun u y =>
    ((hV1 u).differentiable one_ne_zero) y
  -- derivatives of the residual fields
  have da0 : ∀ y v, fderiv ℝ a0 y v = B0009.biotSavart (fun z => fderiv ℝ q z v) 0 y +
      fderiv ℝ (fderiv ℝ Ψ) y v Complex.I := by
    intro y v
    rw [ha0, fderiv_fun_add (hw0dd y) (hVd _ y), add_apply, hw0d,
      fderiv_fderiv_apply hΨ]
  have da1 : ∀ y v, fderiv ℝ a1 y v = B0009.biotSavart (fun z => fderiv ℝ q z v) 1 y -
      fderiv ℝ (fderiv ℝ Ψ) y v 1 := by
    intro y v
    rw [ha1, fderiv_fun_sub (hw1dd y) (hVd _ y), sub_apply, hw1d,
      fderiv_fderiv_apply hΨ]
  -- second derivatives of `Ψ`: Laplacian and symmetry
  have hsymm : ∀ y, fderiv ℝ (fderiv ℝ Ψ) y 1 Complex.I = fderiv ℝ (fderiv ℝ Ψ) y Complex.I 1 :=
    fun y => (hΨ.contDiffAt.isSymmSndFDerivAt (by simp)) 1 Complex.I
  have hL : ∀ y, fderiv ℝ (fderiv ℝ Ψ) y 1 1 + fderiv ℝ (fderiv ℝ Ψ) y Complex.I Complex.I = q y := by
    intro y
    have := hlap y
    simpa [iteratedFDeriv_two_apply] using this
  -- curl and divergence of the residual
  have hcurl : ∀ y, fderiv ℝ a1 y 1 - fderiv ℝ a0 y Complex.I = 0 := by
    intro y
    rw [da1, da0]
    have h1 := hCurl hG y
    have h2 := hL y
    linear_combination h1 - h2
  have hdiv : ∀ y, fderiv ℝ a0 y 1 + fderiv ℝ a1 y Complex.I = 0 := by
    intro y
    rw [da1, da0]
    have h1 := hDiv hG y
    have h2 := hsymm y
    linear_combination h1 + h2
  -- decay of the residual fields
  have e1 : Tendsto a1 (cocompact ℂ) (𝓝 0) := by
    have := (hDec hG 1).sub (tendsto_fderiv_apply hdec 1)
    simpa using this
  have e0 : Tendsto a0 (cocompact ℂ) (𝓝 0) := by
    have := (hDec hG 0).add (tendsto_fderiv_apply hdec Complex.I)
    simpa using this
  -- the two entire functions
  have hfp : ∀ y, (a1 y + Complex.I * a0 y) = 0 := by
    refine eq_zero_of_dbar_eq_zero (f := fun y => a1 y + Complex.I * a0 y)
      (ha1c.add (contDiff_const.mul ha0c)) ?_ ?_
    · intro y
      rw [fderiv_fun_add (ha1d y) ((ha0d y).const_mul _), fderiv_const_mul (ha0d y)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      have h1 := hcurl y
      have h2 := hdiv y
      linear_combination h1 + Complex.I * h2 + (fderiv ℝ a0 y Complex.I) * Complex.I_sq
    · have := e1.add (e0.const_mul Complex.I)
      simpa using this
  have hfm : ∀ y, (starRingEnd ℂ) (a1 y - Complex.I * a0 y) = 0 := by
    refine eq_zero_of_dbar_eq_zero (f := fun y => (starRingEnd ℂ) (a1 y - Complex.I * a0 y))
      (Complex.conjCLE.contDiff.comp (ha1c.sub (contDiff_const.mul ha0c))) ?_ ?_
    · intro y
      have hg : DifferentiableAt ℝ (fun y => a1 y - Complex.I * a0 y) y :=
        (ha1d y).sub ((ha0d y).const_mul _)
      have hc : ∀ v, fderiv ℝ (fun y => (starRingEnd ℂ) (a1 y - Complex.I * a0 y)) y v =
          (starRingEnd ℂ) (fderiv ℝ (fun y => a1 y - Complex.I * a0 y) y v) := by
        intro v
        have := Complex.conjCLE.hasFDerivAt.comp y hg.hasFDerivAt
        have h' : HasFDerivAt (fun y => (starRingEnd ℂ) (a1 y - Complex.I * a0 y)) _ y := this
        rw [h'.fderiv]
        rfl
      rw [hc, hc, fderiv_fun_sub (ha1d y) ((ha0d y).const_mul _), fderiv_const_mul (ha0d y)]
      simp only [sub_apply, smul_apply, smul_eq_mul]
      have h1 := hcurl y
      have h2 := hdiv y
      have key : fderiv ℝ a1 y 1 - Complex.I * fderiv ℝ a0 y 1 -
          Complex.I * (fderiv ℝ a1 y Complex.I - Complex.I * fderiv ℝ a0 y Complex.I) = 0 := by
        linear_combination h1 - Complex.I * h2 + (fderiv ℝ a0 y Complex.I) * Complex.I_sq
      have key' := congrArg (starRingEnd ℂ) key
      simp only [map_sub, map_mul, Complex.conj_I, map_zero] at key'
      simp only [map_sub, map_mul, Complex.conj_I]
      linear_combination key'
    · have h0 : Tendsto (fun y => a1 y - Complex.I * a0 y) (cocompact ℂ) (𝓝 0) := by
        simpa using e1.sub (e0.const_mul Complex.I)
      have h' := (Complex.continuous_conj.tendsto 0).comp h0
      rw [map_zero] at h'
      exact h'
  intro y
  have hp := hfp y
  have hm : a1 y - Complex.I * a0 y = 0 := (map_eq_zero (starRingEnd ℂ)).1 (hfm y)
  have h1 : a1 y = 0 := by linear_combination (hp + hm) / 2
  have h0 : a0 y = 0 := by
    have : Complex.I * a0 y = 0 := by linear_combination (hp - hm) / 2
    simpa using this
  refine ⟨?_, ?_⟩
  · have : B0009.biotSavart q 0 y + fderiv ℝ Ψ y Complex.I = 0 := h0
    linear_combination this
  · have : B0009.biotSavart q 1 y - fderiv ℝ Ψ y 1 = 0 := h1
    linear_combination this

end UnforcedLeray.Short.PartI
