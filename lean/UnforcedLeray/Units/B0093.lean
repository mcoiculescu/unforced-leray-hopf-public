import UnforcedLeray.Analysis.GaussianVortex.PlanarEuler
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Tactic

/-!
# B0093 (`eq:st18-t00067`): Gaussian conjugation of `D` to a harmonic oscillator

Blueprint unit B0093, label `eq:st18-t00067`, `paper/main.tex` lines 1498--1502
(inside the proof of G3a, Section `sec:st18-1665`).

Statement in words. On the plane `ℝ²`, let `G(y) = (4π)⁻¹ e^{-|y|²/4}` be the Gaussian
weight of `eq:st18-t00002` (tex line 649), let `U_G f = f / √G`, and let
`D = Δ + ½ y·∇ + 2` be the operator of `eq:st18-t00011` (tex line 723). Then, for every
twice continuously differentiable function `g` (in particular every smooth or Schwartz
function), with values in any real normed space (in particular `ℂ`), direct
differentiation gives the pointwise identity
`U_G D U_G⁻¹ g = Δ g - (|y|²/16) g + (3/2) g` on all of `ℝ²`. Equivalently, for every
`C²` function `f`, `D f = U_G⁻¹ (Δ - |y|²/16 + 3/2) U_G f`.

The plane is `UnforcedLeray.GaussianVortex.Plane = ℝ × ℝ`, and the partial derivatives are
the classical one-variable Cartesian derivatives, exactly as `GaussianVortex.partialX` and
`GaussianVortex.partialY` (which they extend from real to vector values; see
`dx_eq_partialX`). `|y|²` is `GaussianVortex.radiusSq`.

No integrability enters: the claim is a pointwise calculus identity. The only implicit
hypothesis made explicit is the regularity `ContDiff ℝ 2` of the function on which the
operators act. The weight is strictly positive, so `U_G` involves no division by zero.
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff SchwartzMap

namespace UnforcedLeray.B0093

open UnforcedLeray.GaussianVortex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The operators -/

/-- The classical first Cartesian partial derivative `∂₁`, for vector-valued functions. -/
def dx (f : Plane → E) (z : Plane) : E := deriv (fun x : ℝ => f (x, z.2)) z.1

/-- The classical second Cartesian partial derivative `∂₂`, for vector-valued functions. -/
def dy (f : Plane → E) (z : Plane) : E := deriv (fun y : ℝ => f (z.1, y)) z.2

/-- On real-valued functions `dx` is the library's `partialX`. -/
theorem dx_eq_partialX (f : Plane → ℝ) : dx f = partialX f := rfl

/-- On real-valued functions `dy` is the library's `partialY`. -/
theorem dy_eq_partialY (f : Plane → ℝ) : dy f = partialY f := rfl

/-- The Laplacian `Δ f = ∂₁² f + ∂₂² f`. -/
def laplacian (f : Plane → E) (z : Plane) : E := dx (dx f) z + dy (dy f) z

/-- The Gaussian weight `G(y) = (4π)⁻¹ e^{-|y|²/4}` of `eq:st18-t00002` (tex line 649). -/
def gaussianWeight (z : Plane) : ℝ := (4 * Real.pi)⁻¹ * planarGaussian z

/-- The operator `D = Δ + ½ y·∇ + 2` of `eq:st18-t00011` (tex line 723). -/
def gaussianOperator (f : Plane → E) (z : Plane) : E :=
  laplacian f z + (1 / 2 : ℝ) • (z.1 • dx f z + z.2 • dy f z) + (2 : ℝ) • f z

/-- The conjugation `U_G f = f / √G` (tex line 1498). -/
def conjG (f : Plane → E) (z : Plane) : E := (Real.sqrt (gaussianWeight z))⁻¹ • f z

/-- The inverse conjugation `U_G⁻¹ g = √G g`. -/
def conjGInv (g : Plane → E) (z : Plane) : E := Real.sqrt (gaussianWeight z) • g z

/-- The harmonic oscillator `Δ - |y|²/16 + 3/2` on the right of `eq:st18-t00067`. -/
def oscillator (g : Plane → E) (z : Plane) : E :=
  laplacian g z - (radiusSq z / 16) • g z + (3 / 2 : ℝ) • g z

/-! ## The square root of the weight -/

/-- `c e^{-|y|²/8}`; with `c = (4π)^{-1/2}` it is `√G`. -/
def halfGaussian (c : ℝ) (z : Plane) : ℝ := c * Real.exp (-(radiusSq z / 8))

/-- The normalizing constant `(4π)^{-1/2}` of `√G`. -/
def sqrtConst : ℝ := Real.sqrt (4 * Real.pi)⁻¹

theorem sqrtConst_pos : 0 < sqrtConst := by
  unfold sqrtConst
  have : 0 < (4 * Real.pi)⁻¹ := by positivity
  exact Real.sqrt_pos.mpr this

theorem gaussianWeight_pos (z : Plane) : 0 < gaussianWeight z := by
  unfold gaussianWeight planarGaussian
  positivity

theorem sqrt_gaussianWeight (z : Plane) :
    Real.sqrt (gaussianWeight z) = halfGaussian sqrtConst z := by
  unfold gaussianWeight planarGaussian halfGaussian sqrtConst
  rw [Real.sqrt_mul (by positivity), ← Real.exp_half]
  congr 2
  ring

theorem halfGaussian_pos {c : ℝ} (hc : 0 < c) (z : Plane) : 0 < halfGaussian c z := by
  unfold halfGaussian
  positivity

theorem conjGInv_eq (g : Plane → E) :
    conjGInv g = fun w => halfGaussian sqrtConst w • g w := by
  funext w
  simp only [conjGInv, sqrt_gaussianWeight]

theorem conjG_eq (f : Plane → E) :
    conjG f = fun w => (halfGaussian sqrtConst w)⁻¹ • f w := by
  funext w
  simp only [conjG, sqrt_gaussianWeight]

theorem contDiff_halfGaussian (c : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (halfGaussian c) := by
  unfold halfGaussian radiusSq
  fun_prop

/-! ## One-variable derivatives along coordinate lines -/

theorem hasDerivAt_halfGaussian_x (c x b : ℝ) :
    HasDerivAt (fun t => halfGaussian c (t, b)) (-(x / 4) * halfGaussian c (x, b)) x := by
  convert ((((((hasDerivAt_id x).pow 2).add_const (b ^ 2)).div_const 8).neg).exp).const_mul c
    using 1 <;>
    first | rfl | (dsimp [halfGaussian, radiusSq]; ring)

theorem hasDerivAt_halfGaussian_y (c a y : ℝ) :
    HasDerivAt (fun t => halfGaussian c (a, t)) (-(y / 4) * halfGaussian c (a, y)) y := by
  convert ((((((hasDerivAt_id y).pow 2).const_add (a ^ 2)).div_const 8).neg).exp).const_mul c
    using 1 <;>
    first | rfl | (dsimp [halfGaussian, radiusSq]; ring)

theorem hasDerivAt_quarter (x : ℝ) : HasDerivAt (fun t : ℝ => -(t / 4)) (-(1 / 4)) x := by
  have h : (fun t : ℝ => -(t / 4)) = fun t => t * (-(1 / 4)) := by
    funext t
    ring
  rw [h]
  exact hasDerivAt_mul_const _

theorem hasDerivAt_coeff_x (c x b : ℝ) :
    HasDerivAt (fun t => -(t / 4) * halfGaussian c (t, b))
      ((x ^ 2 / 16 - 1 / 4) * halfGaussian c (x, b)) x := by
  exact ((hasDerivAt_quarter x).mul (hasDerivAt_halfGaussian_x c x b)).congr_deriv (by ring)

theorem hasDerivAt_coeff_y (c a y : ℝ) :
    HasDerivAt (fun t => -(t / 4) * halfGaussian c (a, t))
      ((y ^ 2 / 16 - 1 / 4) * halfGaussian c (a, y)) y := by
  exact ((hasDerivAt_quarter y).mul (hasDerivAt_halfGaussian_y c a y)).congr_deriv (by ring)

theorem hasDerivAt_line_x {f : Plane → E} {x b : ℝ} (hf : DifferentiableAt ℝ f (x, b)) :
    HasDerivAt (fun t : ℝ => f (t, b)) (dx f (x, b)) x := by
  have hl : DifferentiableAt ℝ (fun t : ℝ => ((t, b) : Plane)) x :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  exact (hf.comp x hl).hasDerivAt

theorem hasDerivAt_line_y {f : Plane → E} {a y : ℝ} (hf : DifferentiableAt ℝ f (a, y)) :
    HasDerivAt (fun t : ℝ => f (a, t)) (dy f (a, y)) y := by
  have hl : DifferentiableAt ℝ (fun t : ℝ => ((a, t) : Plane)) y :=
    (differentiableAt_const _).prodMk differentiableAt_id
  exact (hf.comp y hl).hasDerivAt

/-- Adapted from `GaussianVortex.partialX_eq_fderiv` (lean/UnforcedLeray/Analysis/
GaussianVortex/PlanarEuler.lean) to vector values. -/
theorem dx_eq_fderiv {f : Plane → E} {z : Plane} (hf : DifferentiableAt ℝ f z) :
    dx f z = fderiv ℝ f z (1, 0) := by
  simpa only [Function.comp_def, dx, id_eq] using
    (hf.hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv

/-- Adapted from `GaussianVortex.partialY_eq_fderiv` (lean/UnforcedLeray/Analysis/
GaussianVortex/PlanarEuler.lean) to vector values. -/
theorem dy_eq_fderiv {f : Plane → E} {z : Plane} (hf : DifferentiableAt ℝ f z) :
    dy f z = fderiv ℝ f z (0, 1) := by
  simpa only [Function.comp_def, dy, id_eq] using
    (hf.hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv

theorem contDiff_dx {f : Plane → E} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (dx f) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h : dx f = fun z => fderiv ℝ f z (1, 0) := funext fun z => dx_eq_fderiv (hd z)
  rw [h]
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem contDiff_dy {f : Plane → E} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (dy f) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h : dy f = fun z => fderiv ℝ f z (0, 1) := funext fun z => dy_eq_fderiv (hd z)
  rw [h]
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-! ## Derivatives of `φ g` with `φ = c e^{-|y|²/8}` -/

/-- `∂₁(φ g) = -(y₁/4) φ g + φ ∂₁ g`, using `∂₁ φ = -(y₁/4) φ`. -/
theorem dx_halfGaussian_smul (c : ℝ) {g : Plane → E} (hg : Differentiable ℝ g) :
    dx (fun w => halfGaussian c w • g w) =
      fun z => (-(z.1 / 4) * halfGaussian c z) • g z + halfGaussian c z • dx g z := by
  funext z
  obtain ⟨x, b⟩ := z
  have h := (hasDerivAt_halfGaussian_x c x b).fun_smul (hasDerivAt_line_x (hg (x, b)))
  refine h.deriv.trans ?_
  dsimp only
  abel

/-- `∂₂(φ g) = -(y₂/4) φ g + φ ∂₂ g`, using `∂₂ φ = -(y₂/4) φ`. -/
theorem dy_halfGaussian_smul (c : ℝ) {g : Plane → E} (hg : Differentiable ℝ g) :
    dy (fun w => halfGaussian c w • g w) =
      fun z => (-(z.2 / 4) * halfGaussian c z) • g z + halfGaussian c z • dy g z := by
  funext z
  obtain ⟨a, y⟩ := z
  have h := (hasDerivAt_halfGaussian_y c a y).fun_smul (hasDerivAt_line_y (hg (a, y)))
  refine h.deriv.trans ?_
  dsimp only
  abel

theorem dx_dx_halfGaussian_smul (c : ℝ) {g : Plane → E} (hg : ContDiff ℝ 2 g) (z : Plane) :
    dx (dx (fun w => halfGaussian c w • g w)) z =
      ((z.1 ^ 2 / 16 - 1 / 4) * halfGaussian c z) • g z
        + (-(z.1 / 2) * halfGaussian c z) • dx g z + halfGaussian c z • dx (dx g) z := by
  rw [dx_halfGaussian_smul c (hg.differentiable (by norm_num))]
  obtain ⟨x, b⟩ := z
  have h2 := (hasDerivAt_coeff_x c x b).fun_smul
    (hasDerivAt_line_x ((hg.differentiable (by norm_num)) (x, b)))
  have h3 := (hasDerivAt_halfGaussian_x c x b).fun_smul
    (hasDerivAt_line_x (((contDiff_dx hg).differentiable (by norm_num)) (x, b)))
  refine (h2.add h3).deriv.trans ?_
  dsimp only
  module

theorem dy_dy_halfGaussian_smul (c : ℝ) {g : Plane → E} (hg : ContDiff ℝ 2 g) (z : Plane) :
    dy (dy (fun w => halfGaussian c w • g w)) z =
      ((z.2 ^ 2 / 16 - 1 / 4) * halfGaussian c z) • g z
        + (-(z.2 / 2) * halfGaussian c z) • dy g z + halfGaussian c z • dy (dy g) z := by
  rw [dy_halfGaussian_smul c (hg.differentiable (by norm_num))]
  obtain ⟨a, y⟩ := z
  have h2 := (hasDerivAt_coeff_y c a y).fun_smul
    (hasDerivAt_line_y ((hg.differentiable (by norm_num)) (a, y)))
  have h3 := (hasDerivAt_halfGaussian_y c a y).fun_smul
    (hasDerivAt_line_y (((contDiff_dy hg).differentiable (by norm_num)) (a, y)))
  refine (h2.add h3).deriv.trans ?_
  dsimp only
  module

/-- `∂₁ φ = -(y₁/4) φ` for `φ = c e^{-|y|²/8}`. -/
theorem dx_halfGaussian (c : ℝ) (z : Plane) :
    dx (halfGaussian c) z = -(z.1 / 4) * halfGaussian c z :=
  (hasDerivAt_halfGaussian_x c z.1 z.2).deriv

/-- `∂₂ φ = -(y₂/4) φ` for `φ = c e^{-|y|²/8}`. -/
theorem dy_halfGaussian (c : ℝ) (z : Plane) :
    dy (halfGaussian c) z = -(z.2 / 4) * halfGaussian c z :=
  (hasDerivAt_halfGaussian_y c z.1 z.2).deriv

/-- `Δ φ = (|y|²/16 - 1/2) φ` for `φ = c e^{-|y|²/8}` (the blueprint's check). -/
theorem laplacian_halfGaussian (c : ℝ) (z : Plane) :
    laplacian (halfGaussian c) z = (radiusSq z / 16 - 1 / 2) * halfGaussian c z := by
  have e : laplacian (halfGaussian c) z =
      laplacian (fun w => halfGaussian c w • (fun _ : Plane => (1 : ℝ)) w) z := by
    simp only [smul_eq_mul, mul_one]
  rw [e, laplacian, dx_dx_halfGaussian_smul c contDiff_const z,
    dy_dy_halfGaussian_smul c contDiff_const z]
  simp [dx, dy, radiusSq]
  ring

/-- The blueprint's check: `D(φ g) = φ (Δ g - |y|²g/16 + 3g/2)` for `φ = c e^{-|y|²/8}`. -/
theorem gaussianOperator_halfGaussian_smul (c : ℝ) {g : Plane → E} (hg : ContDiff ℝ 2 g)
    (z : Plane) :
    gaussianOperator (fun w => halfGaussian c w • g w) z =
      halfGaussian c z • oscillator g z := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  unfold gaussianOperator oscillator laplacian
  rw [dx_dx_halfGaussian_smul c hg z, dy_dy_halfGaussian_smul c hg z,
    dx_halfGaussian_smul c hd, dy_halfGaussian_smul c hd]
  simp only [radiusSq]
  module

/-! ## The conjugation identity -/

theorem conjG_conjGInv (g : Plane → E) : conjG (conjGInv g) = g := by
  funext z
  simp only [conjG, conjGInv, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (gaussianWeight_pos z)).ne', one_smul]

theorem conjGInv_conjG (f : Plane → E) : conjGInv (conjG f) = f := by
  funext z
  simp only [conjG, conjGInv, smul_smul,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (gaussianWeight_pos z)).ne', one_smul]

/-- `U_G⁻¹` preserves `C^n` regularity. -/
theorem contDiff_conjGInv {n : WithTop ℕ∞} {g : Plane → E} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (conjGInv g) := by
  rw [conjGInv_eq]
  exact (contDiff_halfGaussian sqrtConst).smul hg

/-- `U_G` preserves `C^n` regularity. -/
theorem contDiff_conjG {n : WithTop ℕ∞} {f : Plane → E} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (conjG f) := by
  rw [conjG_eq]
  exact ((contDiff_halfGaussian sqrtConst).inv
    fun w => (halfGaussian_pos sqrtConst_pos w).ne').smul hf

/-- **`eq:st18-t00067` (tex lines 1498--1502).** `U_G D U_G⁻¹ = Δ - |y|²/16 + 3/2`,
pointwise on `ℝ²`, on every `C²` function with values in a real normed space. -/
theorem conjG_gaussianOperator_conjGInv {g : Plane → E} (hg : ContDiff ℝ 2 g) :
    conjG (gaussianOperator (conjGInv g)) = oscillator g := by
  funext z
  rw [conjGInv_eq, conjG, gaussianOperator_halfGaussian_smul _ hg, sqrt_gaussianWeight,
    smul_smul, inv_mul_cancel₀ (halfGaussian_pos sqrtConst_pos z).ne', one_smul]

/-- **`eq:st18-t00067` (tex line 1500), equivalent form.** For every `C²` function `f`,
`D f = U_G⁻¹ (Δ - |y|²/16 + 3/2) U_G f`. -/
theorem gaussianOperator_eq_conj {f : Plane → E} (hf : ContDiff ℝ 2 f) :
    gaussianOperator f = conjGInv (oscillator (conjG f)) := by
  rw [← conjG_gaussianOperator_conjGInv (contDiff_conjG hf), conjGInv_conjG,
    conjGInv_conjG]

/-- **`eq:st18-t00067` (tex line 1500) on smooth complex-valued functions.** -/
theorem conjG_gaussianOperator_conjGInv_smooth {g : Plane → ℂ} (hg : ContDiff ℝ ∞ g) :
    conjG (gaussianOperator (conjGInv g)) = oscillator g :=
  conjG_gaussianOperator_conjGInv (contDiff_infty.mp hg 2)

/-- **`eq:st18-t00067` (tex line 1500) on Schwartz functions**, the core used at
tex lines 1503--1505. -/
theorem conjG_gaussianOperator_conjGInv_schwartz (g : 𝓢(Plane, ℂ)) :
    conjG (gaussianOperator (conjGInv (g : Plane → ℂ))) = oscillator (g : Plane → ℂ) :=
  conjG_gaussianOperator_conjGInv (g.smooth 2)

end UnforcedLeray.B0093
