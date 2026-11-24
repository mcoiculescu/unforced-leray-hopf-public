import UnforcedLeray.Units.B0221.Conjugation

/-!
# B0222 helper: the Leibniz rule for the outer operator

Blueprint unit B0222 (label `eq:st18-t00115`), `paper/main.tex` lines 3327–3339; infrastructure
INF23 (cylindrical vector Laplacian for no-swirl fields, chain rule).

A Cartesian component of the meridional lift `a (b_r e_r + b_z e_z)` (B0220, `fieldU`) is a
product `g(x) W(x, τ)` of a component `g` of the frame vector `e_r` (independent of `τ`) and a
scalar lift `W = a b_r` (B0220, `liftU`). This file gives the Leibniz rule for the outer operator
`L = ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ` of B0221 (`outerGen`, tex lines 3343–3347) on such a product:

  `L(g W) = g L W + ν ε² (Δg · W + 2 ∇g·∇W) + ((x·∇) g / 2) W`   (`outerGen_mul`).

The second derivatives are reduced to one-variable second derivatives along coordinate lines
(`B0221.secondPartial_eq_deriv_deriv`), where the Leibniz rule is `deriv_deriv_mul`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open UnforcedLeray.B0220 UnforcedLeray.B0221

namespace UnforcedLeray.B0222

/-! ### One variable -/

/-- The derivative of a `C²` function of one variable is differentiable. -/
theorem differentiableAt_deriv_of_contDiffAt {f : ℝ → ℝ} {t0 : ℝ} (hf : ContDiffAt ℝ 2 f t0) :
    DifferentiableAt ℝ (deriv f) t0 := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) t0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact hD.clm_apply (differentiableAt_const _)

/-- The Leibniz rule for the second derivative: `(fg)'' = f''g + 2f'g' + fg''`. -/
theorem deriv_deriv_mul {f g : ℝ → ℝ} {t0 : ℝ} (hf : ContDiffAt ℝ 2 f t0)
    (hg : ContDiffAt ℝ 2 g t0) :
    deriv (deriv fun t => f t * g t) t0 =
      deriv (deriv f) t0 * g t0 + 2 * (deriv f t0 * deriv g t0) +
        f t0 * deriv (deriv g) t0 := by
  have hfe : ∀ᶠ t in 𝓝 t0, DifferentiableAt ℝ f t :=
    (hf.eventually (by simp)).mono fun t ht => ht.differentiableAt (by norm_num)
  have hge : ∀ᶠ t in 𝓝 t0, DifferentiableAt ℝ g t :=
    (hg.eventually (by simp)).mono fun t ht => ht.differentiableAt (by norm_num)
  have h1 : deriv (fun t => f t * g t) =ᶠ[𝓝 t0]
      fun t => deriv f t * g t + f t * deriv g t := by
    filter_upwards [hfe, hge] with t hft hgt
    exact deriv_mul hft hgt
  rw [h1.deriv_eq]
  have hf1 : DifferentiableAt ℝ f t0 := hf.differentiableAt (by norm_num)
  have hg1 : DifferentiableAt ℝ g t0 := hg.differentiableAt (by norm_num)
  have hf2 := differentiableAt_deriv_of_contDiffAt hf
  have hg2 := differentiableAt_deriv_of_contDiffAt hg
  have h3 : HasDerivAt (fun t => deriv f t * g t + f t * deriv g t) _ t0 :=
    (hf2.hasDerivAt.mul hg1.hasDerivAt).add (hf1.hasDerivAt.mul hg2.hasDerivAt)
  rw [h3.deriv]
  ring

/-- Restriction of a `C²` function to the line `t ↦ x + t v`. -/
theorem contDiffAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    {x : E} (hF : ContDiffAt ℝ 2 F x) (v : E) :
    ContDiffAt ℝ 2 (fun t : ℝ => F (x + t • v)) 0 := by
  have hF' : ContDiffAt ℝ 2 F (x + (0 : ℝ) • v) := by simpa using hF
  have hl : ContDiffAt ℝ 2 (fun t : ℝ => x + t • v) 0 := by fun_prop
  exact hF'.comp (0 : ℝ) hl

/-! ### Products on `ℝ³` -/

/-- The Laplacian of a function on `ℝ³`, as the sum of the second coordinate derivatives. -/
def lapFun (g : Space → ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ g y (coordinateVector i)) x (coordinateVector i)

/-- The Leibniz rule for a second directional derivative. -/
theorem secondPartial_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g W : E → ℝ}
    {x : E} (hg : ContDiffAt ℝ 2 g x) (hW : ContDiffAt ℝ 2 W x) (v : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun x' => g x' * W x') y v) x v =
      fderiv ℝ (fun y => fderiv ℝ g y v) x v * W x + 2 * (fderiv ℝ g x v * fderiv ℝ W x v) +
        g x * fderiv ℝ (fun y => fderiv ℝ W y v) x v := by
  have hgW : ContDiffAt ℝ 2 (fun x' => g x' * W x') x := hg.mul hW
  rw [secondPartial_eq_deriv_deriv hgW, secondPartial_eq_deriv_deriv hg,
    secondPartial_eq_deriv_deriv hW, fderiv_eq_deriv_line (hg.differentiableAt (by norm_num)),
    fderiv_eq_deriv_line (hW.differentiableAt (by norm_num))]
  have h := deriv_deriv_mul (contDiffAt_line hg v) (contDiffAt_line hW v)
  simp only [zero_smul, add_zero] at h
  exact h

/-- The first spatial partial derivative of a product `g(x) W(x, τ)`. -/
theorem spatialPartial_mul {g : Space → ℝ} {W : Space × ℝ → ℝ} {x : Space} {τ : ℝ}
    (hg : DifferentiableAt ℝ g x) (hW : DifferentiableAt ℝ (fun x' => W (x', τ)) x)
    (i : Fin 3) :
    spatialPartial (fun y => g y.1 * W y) i (x, τ) =
      fderiv ℝ g x (coordinateVector i) * W (x, τ) + g x * spatialPartial W i (x, τ) := by
  simp only [spatialPartial]
  have h : HasFDerivAt (fun x' => g x' * W (x', τ)) _ x := hg.hasFDerivAt.mul hW.hasFDerivAt
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The spatial Laplacian of a product `g(x) W(x, τ)`:
`Δ(gW) = Δg · W + 2 ∇g·∇W + g ΔW`. -/
theorem spatialLap_mul {g : Space → ℝ} {W : Space × ℝ → ℝ} {x : Space} {τ : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hW : ContDiffAt ℝ 2 (fun x' => W (x', τ)) x) :
    spatialLap (fun y => g y.1 * W y) (x, τ) =
      lapFun g x * W (x, τ) +
        2 * ∑ i : Fin 3, fderiv ℝ g x (coordinateVector i) * spatialPartial W i (x, τ) +
        g x * spatialLap W (x, τ) := by
  simp only [spatialLap, spatialPartial, lapFun, Fin.sum_univ_three]
  rw [secondPartial_mul hg hW, secondPartial_mul hg hW, secondPartial_mul hg hW]
  ring

/-- The phase derivative of a product `g(x) W(x, τ)`. -/
theorem timePartial_mul (g : Space → ℝ) (W : Space × ℝ → ℝ) (y : Space × ℝ) :
    timePartial (fun y => g y.1 * W y) y = g y.1 * timePartial W y := by
  simp only [timePartial]
  exact deriv_const_mul_field (g y.1)

/-- **Leibniz rule for the outer operator** `L = ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ` on a product
`g(x) W(x, τ)` with `g` independent of `τ`:
`L(gW) = g LW + ν ε² (Δg · W + 2 ∇g·∇W) + ((x·∇)g / 2) W`. -/
theorem outerGen_mul (ν ε : ℝ) {g : Space → ℝ} {W : Space × ℝ → ℝ} {x : Space} {τ : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hW : ContDiffAt ℝ 2 (fun x' => W (x', τ)) x) :
    outerGen ν ε (fun y => g y.1 * W y) (x, τ) =
      g x * outerGen ν ε W (x, τ) +
        ν * ε ^ 2 * (lapFun g x * W (x, τ) +
          2 * ∑ i : Fin 3, fderiv ℝ g x (coordinateVector i) * spatialPartial W i (x, τ)) +
        (∑ i : Fin 3, x i * fderiv ℝ g x (coordinateVector i)) / 2 * W (x, τ) := by
  have hg1 : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hW1 : DifferentiableAt ℝ (fun x' => W (x', τ)) x := hW.differentiableAt (by norm_num)
  simp only [outerGen]
  rw [spatialLap_mul hg hW, timePartial_mul]
  simp only [Fin.sum_univ_three, spatialPartial_mul hg1 hW1]
  ring

end UnforcedLeray.B0222
