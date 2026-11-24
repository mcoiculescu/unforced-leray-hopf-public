import UnforcedLeray.Analysis.Pressure.NewtonIdentity

/-!
# B0635 (`eq:affine-4-82`, tex lines 12288–12292): fourth Newton derivative at `(r,0,0)`

Unit B0635 of `paper/main.tex` (blueprint label `eq:affine-4-82`), tex lines 12288–12292, in
the proof of `lem:affine-leading-jet` (line 12226, section `sec:st18-14224`), where it feeds the
leading physical jet `eq:affine-4-83`.

Statement in words. Let `N(x) = (4π|x|)⁻¹` be the Newton potential on `ℝ³` and let
`x = (r,0,0)` with `r > 0`. Then the Hessian of the third-third second derivative of `N`
at `x` is diagonal:
`D² ∂₃₃ N(x) = (4π r⁵)⁻¹ diag(-12, 3, 9)`, i.e.
`∂ᵢ ∂ⱼ ∂₃ ∂₃ N(x) = (4π r⁵)⁻¹ dᵢⱼ` with `d = diag(-12, 3, 9)` (trace zero).

Formal setting.
* `N` is the project's `UnforcedLeray.PressureAnalysis.newtonPotential`,
  `x ↦ 1 / (4π ‖x‖)` on `Space = EuclideanSpace ℝ (Fin 3)`. Its value `0` at the origin
  (real division by `0`) is irrelevant: every derivative below is taken at a point `y ≠ 0`, and
  all identities used are local on the open set `{y ≠ 0}`.
* The manuscript coordinates `1, 2, 3` are the Lean indices `0, 1, 2`; `∂₃` is the
  derivative along `coordinateVector 2`. The point is any `x` with `x 0 = r`, `x 1 = 0`,
  `x 2 = 0` (equivalently `x = EuclideanSpace.single 0 r`).
* Two forms are proved: nested coordinate Fréchet derivatives
  (`spatialTestDerivative i (spatialTestDerivative j (∂₃ (∂₃ N))) x`), and the fourth
  iterated Fréchet derivative `iteratedFDeriv ℝ 4 N x ![eᵢ, eⱼ, e₃, e₃]`. Both are genuine:
  `N` is `C^∞` on `{y ≠ 0}` (`contDiffAt_newtonPotential`), and the intermediate derivatives are
  identified with explicit formulas there, so no junk value of `fderiv` enters.

Main declarations: `hessian_d33_newtonPotential_axial` (coordinate form),
`hessianMatrix_d33_newtonPotential_axial` (matrix form), `iteratedFDeriv_newtonPotential_axial`
and `iteratedFDeriv_newtonPotential_single` (fourth Fréchet derivative form), and
`trace_hessian_d33_newtonPotential_axial` (trace zero, from the proof outline).

The explicit intermediate formulas (with `c = (4π)⁻¹`, `ρ = ‖y‖⁻¹`):
`∂₃N = -c y₃ ρ³`, `∂₃₃N = -c ρ³ + 3c y₃² ρ⁵`,
`∂ⱼ∂₃₃N = (3c yⱼ + 6c y₃ δⱼ₃) ρ⁵ - 15c y₃² yⱼ ρ⁷`.
-/

set_option autoImplicit false

noncomputable section

open scoped RealInnerProductSpace Topology ContDiff
open Filter

namespace UnforcedLeray.B0635

open UnforcedLeray UnforcedLeray.PressureAnalysis

/-! ## Derivative of `‖y‖⁻¹ ^ m` times a differentiable prefactor -/

/-- The inverse norm has derivative `v ↦ -‖y‖⁻³ ⟪y, v⟫` away from the origin. -/
theorem hasFDerivAt_invNorm {y : Space} (hy : y ≠ 0) :
    HasFDerivAt (fun z : Space => ‖z‖⁻¹) (-(‖y‖⁻¹ ^ 3) • innerSL ℝ y) y := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have h := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.rpow_const
    (p := -(1 : ℝ) / 2) (Or.inl (pow_ne_zero 2 hn))
  have he : (fun z : Space => (‖z‖ ^ 2) ^ (-(1 : ℝ) / 2)) = fun z => ‖z‖⁻¹ := by
    funext z
    exact norm_sq_rpow_neg_half z
  rw [he, norm_sq_rpow_neg_three_halves] at h
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

/-- Product rule for a prefactor times `‖z‖⁻¹ ^ m`, away from the origin. -/
theorem hasFDerivAt_mul_invNorm_pow {a : Space → ℝ} {a' : Space →L[ℝ] ℝ} {y : Space}
    (hy : y ≠ 0) (ha : HasFDerivAt a a' y) (m : ℕ) :
    HasFDerivAt (fun z => a z * ‖z‖⁻¹ ^ m)
      (‖y‖⁻¹ ^ m • a' - ((m : ℝ) * a y * ‖y‖⁻¹ ^ (m + 2)) • innerSL ℝ y) y := by
  have h := ha.fun_mul ((hasFDerivAt_invNorm hy).pow m)
  refine h.congr_fderiv ?_
  ext v
  rcases m with _ | m
  · simp
  · simp
    ring

/-- The coordinate function `z ↦ z k` is its own derivative. -/
theorem hasFDerivAt_coord (k : Fin 3) (y : Space) :
    HasFDerivAt (fun z : Space => z k) (EuclideanSpace.proj k : Space →L[ℝ] ℝ) y :=
  (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt

/-! ## Explicit formulas on `{y ≠ 0}` -/

/-- `∂₃ N = -(4π)⁻¹ y₃ ‖y‖⁻³` (manuscript `∂₃`, Lean index `2`). -/
def d3N (z : Space) : ℝ := (-(4 * Real.pi)⁻¹ * z 2) * ‖z‖⁻¹ ^ 3

/-- `∂₃₃ N = (4π)⁻¹ (3 y₃² ‖y‖⁻⁵ - ‖y‖⁻³)`. -/
def d33N (z : Space) : ℝ :=
  (-(4 * Real.pi)⁻¹) * ‖z‖⁻¹ ^ 3 + (3 * (4 * Real.pi)⁻¹ * z 2 ^ 2) * ‖z‖⁻¹ ^ 5

/-- `∂ⱼ ∂₃₃ N = (4π)⁻¹ ((3 yⱼ + 6 y₃ δⱼ₃) ‖y‖⁻⁵ - 15 y₃² yⱼ ‖y‖⁻⁷)`. -/
def dj33N (j : Fin 3) (z : Space) : ℝ :=
  (3 * (4 * Real.pi)⁻¹ * z j + 6 * (4 * Real.pi)⁻¹ * z 2 * (coordinateVector j) 2) *
      ‖z‖⁻¹ ^ 5 +
    (-15 * (4 * Real.pi)⁻¹ * z 2 ^ 2 * z j) * ‖z‖⁻¹ ^ 7

theorem newtonPotential_eq_invNorm :
    newtonPotential = fun z : Space => (4 * Real.pi)⁻¹ * ‖z‖⁻¹ ^ 1 := by
  funext z
  simp [newtonPotential, mul_comm]

theorem inner_coordinateVector (y : Space) (k : Fin 3) :
    ⟪y, coordinateVector k⟫ = y k := by
  simp [coordinateVector, EuclideanSpace.inner_single_right]

theorem d3N_eq {y : Space} (hy : y ≠ 0) :
    spatialTestDerivative 2 newtonPotential y = d3N y := by
  unfold spatialTestDerivative
  rw [newtonPotential_eq_invNorm,
    (hasFDerivAt_mul_invNorm_pow hy (hasFDerivAt_const ((4 * Real.pi)⁻¹) y) 1).fderiv]
  simp [d3N, inner_coordinateVector]
  ring

theorem d33N_eq {y : Space} (hy : y ≠ 0) :
    spatialTestDerivative 2 d3N y = d33N y := by
  unfold spatialTestDerivative
  have h := hasFDerivAt_mul_invNorm_pow hy
    ((hasFDerivAt_coord 2 y).const_mul (-(4 * Real.pi)⁻¹)) 3
  have he : d3N = fun z : Space => (-(4 * Real.pi)⁻¹ * z 2) * ‖z‖⁻¹ ^ 3 := rfl
  rw [he, h.fderiv]
  simp only [sub_apply, smul_apply, innerSL_apply_apply,
    inner_coordinateVector]
  simp [d33N, coordinateVector]
  ring

theorem dj33N_eq (j : Fin 3) {y : Space} (hy : y ≠ 0) :
    spatialTestDerivative j d33N y = dj33N j y := by
  unfold spatialTestDerivative
  have h1 := hasFDerivAt_mul_invNorm_pow hy (hasFDerivAt_const (-(4 * Real.pi)⁻¹) y) 3
  have h2 := hasFDerivAt_mul_invNorm_pow hy
    (((hasFDerivAt_coord 2 y).pow 2).const_mul (3 * (4 * Real.pi)⁻¹)) 5
  have he : d33N = fun z : Space =>
      (-(4 * Real.pi)⁻¹) * ‖z‖⁻¹ ^ 3 + (3 * (4 * Real.pi)⁻¹ * z 2 ^ 2) * ‖z‖⁻¹ ^ 5 := rfl
  rw [he, (h1.fun_add h2).fderiv]
  simp [dj33N, inner_coordinateVector]
  ring

/-! ## The last derivative at the axial point -/

theorem norm_axial {r : ℝ} (hr : 0 < r) {x : Space} (hx0 : x 0 = r) (hx1 : x 1 = 0)
    (hx2 : x 2 = 0) : ‖x‖ = r := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, hx0, hx1, hx2]
  simp [Real.sqrt_sq hr.le]

theorem deriv_dj33N_axial {r : ℝ} (hr : 0 < r) {x : Space} (hx0 : x 0 = r) (hx1 : x 1 = 0)
    (hx2 : x 2 = 0) (i j : Fin 3) :
    spatialTestDerivative i (dj33N j) x =
      (4 * Real.pi * r ^ 5)⁻¹ * Matrix.diagonal ![(-12 : ℝ), 3, 9] i j := by
  have hn : ‖x‖ = r := norm_axial hr hx0 hx1 hx2
  have hx : x ≠ 0 := by
    rw [← norm_pos_iff, hn]
    exact hr
  unfold spatialTestDerivative
  have h1 := hasFDerivAt_mul_invNorm_pow hx
    (((hasFDerivAt_coord j x).const_mul (3 * (4 * Real.pi)⁻¹)).fun_add
      (((hasFDerivAt_coord 2 x).const_mul (6 * (4 * Real.pi)⁻¹)).mul_const
        ((coordinateVector j) 2))) 5
  have h2 := hasFDerivAt_mul_invNorm_pow hx
    ((((hasFDerivAt_coord 2 x).pow 2).const_mul (-15 * (4 * Real.pi)⁻¹)).fun_mul
      (hasFDerivAt_coord j x)) 7
  have he : dj33N j = fun z : Space =>
      (3 * (4 * Real.pi)⁻¹ * z j + 6 * (4 * Real.pi)⁻¹ * z 2 * (coordinateVector j) 2) *
          ‖z‖⁻¹ ^ 5 +
        (-15 * (4 * Real.pi)⁻¹ * z 2 ^ 2 * z j) * ‖z‖⁻¹ ^ 7 := rfl
  rw [he, (h1.fun_add h2).fderiv]
  simp only [add_apply, sub_apply, smul_apply, innerSL_apply_apply, inner_coordinateVector]
  simp only [hn, hx2]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hr0 : r ≠ 0 := hr.ne'
  fin_cases i <;> fin_cases j <;> simp [hx0, hx1, hx2, coordinateVector] <;>
    (try field_simp) <;> ring

/-! ## The unit: `D² ∂₃₃ N(r,0,0) = (4π r⁵)⁻¹ diag(-12, 3, 9)` -/

theorem spatialTestDerivative_congr_of_ne {f g : Space → ℝ}
    (hfg : ∀ y : Space, y ≠ 0 → f y = g y) {x : Space} (hx : x ≠ 0) (k : Fin 3) :
    spatialTestDerivative k f x = spatialTestDerivative k g x := by
  unfold spatialTestDerivative
  rw [Filter.EventuallyEq.fderiv_eq ((eventually_ne_nhds hx).mono hfg)]

/-- `∂₃∂₃N = (4π)⁻¹ (3 y₃² ‖y‖⁻⁵ - ‖y‖⁻³)` on `{y ≠ 0}`. -/
theorem d33_newtonPotential_eq {y : Space} (hy : y ≠ 0) :
    spatialTestDerivative 2 (spatialTestDerivative 2 newtonPotential) y = d33N y := by
  rw [spatialTestDerivative_congr_of_ne (fun z hz => d3N_eq hz) hy]
  exact d33N_eq hy

/-- `∂ⱼ∂₃∂₃N` on `{y ≠ 0}`. -/
theorem dj33_newtonPotential_eq (j : Fin 3) {y : Space} (hy : y ≠ 0) :
    spatialTestDerivative j (spatialTestDerivative 2 (spatialTestDerivative 2 newtonPotential))
      y = dj33N j y := by
  rw [spatialTestDerivative_congr_of_ne (fun z hz => d33_newtonPotential_eq hz) hy]
  exact dj33N_eq j hy

/-- **B0635 (`eq:affine-4-82`, tex line 12290), coordinate form.** For `N(x) = (4π|x|)⁻¹` and
`x = (r,0,0)` with `r > 0`, `∂ᵢ ∂ⱼ ∂₃ ∂₃ N(x) = (4π r⁵)⁻¹ diag(-12, 3, 9)ᵢⱼ`. The manuscript
coordinate `3` is the Lean index `2`. -/
theorem hessian_d33_newtonPotential_axial {r : ℝ} (hr : 0 < r) {x : Space} (hx0 : x 0 = r)
    (hx1 : x 1 = 0) (hx2 : x 2 = 0) (i j : Fin 3) :
    spatialTestDerivative i
        (spatialTestDerivative j (spatialTestDerivative 2 (spatialTestDerivative 2 newtonPotential)))
        x =
      (4 * Real.pi * r ^ 5)⁻¹ * Matrix.diagonal ![(-12 : ℝ), 3, 9] i j := by
  have hx : x ≠ 0 := by
    rw [← norm_pos_iff, norm_axial hr hx0 hx1 hx2]
    exact hr
  rw [spatialTestDerivative_congr_of_ne (fun z hz => dj33_newtonPotential_eq j hz) hx]
  exact deriv_dj33N_axial hr hx0 hx1 hx2 i j

/-- **B0635, matrix form.** The Hessian matrix of `∂₃₃N` at `(r,0,0)` is
`(4π r⁵)⁻¹ • diag(-12, 3, 9)` (tex line 12290). -/
theorem hessianMatrix_d33_newtonPotential_axial {r : ℝ} (hr : 0 < r) {x : Space}
    (hx0 : x 0 = r) (hx1 : x 1 = 0) (hx2 : x 2 = 0) :
    (Matrix.of fun i j : Fin 3 => spatialTestDerivative i
        (spatialTestDerivative j (spatialTestDerivative 2 (spatialTestDerivative 2 newtonPotential)))
        x) =
      (4 * Real.pi * r ^ 5)⁻¹ • Matrix.diagonal ![(-12 : ℝ), 3, 9] := by
  ext i j
  rw [Matrix.of_apply, hessian_d33_newtonPotential_axial hr hx0 hx1 hx2 i j, Matrix.smul_apply,
    smul_eq_mul]

/-- The trace of `D²∂₃₃N(r,0,0)` vanishes (`∂₃₃ΔN = 0` off the origin), as noted with the
proof outline of tex line 12290. -/
theorem trace_hessian_d33_newtonPotential_axial {r : ℝ} (hr : 0 < r) {x : Space}
    (hx0 : x 0 = r) (hx1 : x 1 = 0) (hx2 : x 2 = 0) :
    ∑ i : Fin 3, spatialTestDerivative i
        (spatialTestDerivative i (spatialTestDerivative 2 (spatialTestDerivative 2 newtonPotential)))
        x = 0 := by
  simp only [hessian_d33_newtonPotential_axial hr hx0 hx1 hx2, Fin.sum_univ_three,
    Matrix.diagonal_apply_eq]
  simp
  ring

/-! ## The same identity for the fourth iterated Fréchet derivative -/

/-- Nested directional derivatives `∂_{m 0} ∂_{m 1} ⋯ ∂_{m (n-1)} f`, outermost first. -/
def nestedDeriv : (n : ℕ) → (Fin n → Space) → (Space → ℝ) → Space → ℝ
  | 0, _, f => f
  | n + 1, m, f => fun y => fderiv ℝ (nestedDeriv n (Fin.tail m) f) y (m 0)

theorem contDiffAt_newtonPotential {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ ∞ newtonPotential y := by
  rw [newtonPotential_eq_invNorm]
  exact contDiffAt_const.mul
    (((contDiffAt_norm ℝ hy).inv (norm_ne_zero_iff.mpr hy)).pow 1)

/-- On `{y ≠ 0}`, where `f` is smooth, the iterated Fréchet derivative is the nested
directional derivative. -/
theorem iteratedFDeriv_eq_nestedDeriv {f : Space → ℝ}
    (hf : ∀ y : Space, y ≠ 0 → ContDiffAt ℝ ∞ f y) :
    ∀ (n : ℕ) (m : Fin n → Space) (y : Space), y ≠ 0 →
      iteratedFDeriv ℝ n f y m = nestedDeriv n m f y
  | 0 => by
    intro m y _
    simp [nestedDeriv]
  | n + 1 => by
    intro m y hy
    rw [((hf y hy).differentiableAt_iteratedFDeriv
      (mod_cast ENat.natCast_lt_top n)).iteratedFDeriv_succ_apply_left']
    simp only [nestedDeriv]
    rw [Filter.EventuallyEq.fderiv_eq ((eventually_ne_nhds hy).mono
      fun z hz => iteratedFDeriv_eq_nestedDeriv hf n (Fin.tail m) z hz)]

/-- **B0635 (`eq:affine-4-82`, tex line 12290), Fréchet form.** For `x = (r,0,0)`, `r > 0`,
`D⁴N(x)[eᵢ, eⱼ, e₃, e₃] = (4π r⁵)⁻¹ diag(-12, 3, 9)ᵢⱼ`, i.e. `D²∂₃₃N(x)` is
`(4π r⁵)⁻¹ diag(-12, 3, 9)`. -/
theorem iteratedFDeriv_newtonPotential_axial {r : ℝ} (hr : 0 < r) {x : Space} (hx0 : x 0 = r)
    (hx1 : x 1 = 0) (hx2 : x 2 = 0) (i j : Fin 3) :
    iteratedFDeriv ℝ 4 newtonPotential x
        ![coordinateVector i, coordinateVector j, coordinateVector 2, coordinateVector 2] =
      (4 * Real.pi * r ^ 5)⁻¹ * Matrix.diagonal ![(-12 : ℝ), 3, 9] i j := by
  have hx : x ≠ 0 := by
    rw [← norm_pos_iff, norm_axial hr hx0 hx1 hx2]
    exact hr
  rw [iteratedFDeriv_eq_nestedDeriv (fun y hy => contDiffAt_newtonPotential hy) 4 _ x hx]
  exact hessian_d33_newtonPotential_axial hr hx0 hx1 hx2 i j

/-- The point `(r,0,0)` written as `EuclideanSpace.single 0 r`. -/
theorem iteratedFDeriv_newtonPotential_single {r : ℝ} (hr : 0 < r) (i j : Fin 3) :
    iteratedFDeriv ℝ 4 newtonPotential (EuclideanSpace.single 0 r)
        ![coordinateVector i, coordinateVector j, coordinateVector 2, coordinateVector 2] =
      (4 * Real.pi * r ^ 5)⁻¹ * Matrix.diagonal ![(-12 : ℝ), 3, 9] i j :=
  iteratedFDeriv_newtonPotential_axial hr (by simp) (by simp) (by simp) i j

end UnforcedLeray.B0635
