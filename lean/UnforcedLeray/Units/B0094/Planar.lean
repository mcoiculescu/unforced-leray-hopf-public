import UnforcedLeray.Units.B0093
import UnforcedLeray.Units.B0094.Profiles
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# B0094 helper: the planar operator `D = Δ + ½ y·∇ + 2` on the Gaussian-polynomial core

Blueprint unit B0094 (`eq:st18-t00068`, `paper/main.tex` lines 1503--1515); the operator `D`
is `eq:st18-t00011` (tex line 723), formalized as `B0093.gaussianOperator`.

For a profile `q(s)` of `s = |y|²`, the angular-two planar function
`F(y) = (y₁ + i y₂)² q(|y|²)` satisfies, by direct differentiation,
`D F = (y₁ + i y₂)² (4 s q'' + (12 + s) q' + 3 q)` (`gaussianOperator_angF`).
For `q(s) = p(s) e^{-s/4}` the bracket is `(lag p)(s) e^{-s/4}`, and
`F = angularTwoField (profFun p)` is the planar realization `f₂(r) e^{2iϑ}` (B0010) of the profile
`f₂ = r² p(r²) e^{-r²/4}`. Hence (`gaussianOperator_angularTwoField_profFun`)

  `D (angularTwoField (profFun p)) = angularTwoField (profFun (lag p))` on all of `ℝ²`,

i.e. the core operator `Dcore : prof p ↦ prof (lag p)` is the manuscript's `D` acting on the
angular-two functions `r² p(r²) e^{-r²/4} e^{2iϑ}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial

namespace UnforcedLeray.B0094

open UnforcedLeray.B0010 UnforcedLeray.GaussianVortex

/-- `w(y) = y₁ + i y₂`. -/
def wz (z : ℝ × ℝ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- `s(y) = |y|²`. -/
def sz (z : ℝ × ℝ) : ℝ := z.1 ^ 2 + z.2 ^ 2

/-- The angular-two planar function `w(y)² q(|y|²)`. -/
def angF (q : ℝ → ℂ) (z : ℝ × ℝ) : ℂ := wz z ^ 2 * q (sz z)

section Calculus

variable (q q' q'' : ℝ → ℂ)

theorem hasDerivAt_wz_x (x y : ℝ) : HasDerivAt (fun x : ℝ => wz (x, y)) 1 x := by
  have := ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * Complex.I)
  simpa [wz] using this

theorem hasDerivAt_wz_y (x y : ℝ) : HasDerivAt (fun y : ℝ => wz (x, y)) Complex.I y := by
  have := (((hasDerivAt_id y).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)
  simpa [wz] using this

theorem hasDerivAt_ofReal (x : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
  simpa using (hasDerivAt_id x).ofReal_comp

theorem hasDerivAt_comp_sz_x (hq : ∀ s, HasDerivAt q (q' s) s) (x y : ℝ) :
    HasDerivAt (fun x : ℝ => q (sz (x, y))) (2 * (x : ℂ) * q' (sz (x, y))) x := by
  have h2 : HasDerivAt (fun x : ℝ => sz (x, y)) (2 * x) x := by
    have := (hasDerivAt_pow 2 x).add_const (y ^ 2)
    simpa [sz] using this
  refine ((hq (sz (x, y))).scomp x h2).congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

theorem hasDerivAt_comp_sz_y (hq : ∀ s, HasDerivAt q (q' s) s) (x y : ℝ) :
    HasDerivAt (fun y : ℝ => q (sz (x, y))) (2 * (y : ℂ) * q' (sz (x, y))) y := by
  have h2 : HasDerivAt (fun y : ℝ => sz (x, y)) (2 * y) y := by
    have := (hasDerivAt_pow 2 y).const_add (x ^ 2)
    simpa [sz] using this
  refine ((hq (sz (x, y))).scomp y h2).congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

/-- `∂₁ F = 2 w q + 2 y₁ w² q'`. -/
theorem dx_angF (hq : ∀ s, HasDerivAt q (q' s) s) :
    B0093.dx (angF q) =
      fun z => 2 * wz z * q (sz z) + 2 * (z.1 : ℂ) * wz z ^ 2 * q' (sz z) := by
  funext z
  have h := ((hasDerivAt_wz_x z.1 z.2).pow 2).mul (hasDerivAt_comp_sz_x q q' hq z.1 z.2)
  have h' : HasDerivAt (fun x : ℝ => angF q (x, z.2))
      (2 * wz z * q (sz z) + 2 * (z.1 : ℂ) * wz z ^ 2 * q' (sz z)) z.1 := by
    refine h.congr_deriv ?_
    simp only [Prod.mk.eta, Pi.pow_apply]
    push_cast
    ring
  exact h'.deriv

/-- `∂₂ F = 2 i w q + 2 y₂ w² q'`. -/
theorem dy_angF (hq : ∀ s, HasDerivAt q (q' s) s) :
    B0093.dy (angF q) =
      fun z => 2 * Complex.I * wz z * q (sz z) + 2 * (z.2 : ℂ) * wz z ^ 2 * q' (sz z) := by
  funext z
  have h := ((hasDerivAt_wz_y z.1 z.2).pow 2).mul (hasDerivAt_comp_sz_y q q' hq z.1 z.2)
  have h' : HasDerivAt (fun y : ℝ => angF q (z.1, y))
      (2 * Complex.I * wz z * q (sz z) + 2 * (z.2 : ℂ) * wz z ^ 2 * q' (sz z)) z.2 := by
    refine h.congr_deriv ?_
    simp only [Prod.mk.eta, Pi.pow_apply]
    push_cast
    ring
  exact h'.deriv

theorem dxdx_angF (hq : ∀ s, HasDerivAt q (q' s) s) (hq' : ∀ s, HasDerivAt q' (q'' s) s)
    (z : ℝ × ℝ) :
    B0093.dx (B0093.dx (angF q)) z =
      2 * q (sz z) + 8 * (z.1 : ℂ) * wz z * q' (sz z) + 2 * wz z ^ 2 * q' (sz z) +
        4 * (z.1 : ℂ) ^ 2 * wz z ^ 2 * q'' (sz z) := by
  rw [dx_angF q q' hq]
  have hw := hasDerivAt_wz_x z.1 z.2
  have hx := hasDerivAt_ofReal z.1
  have hqs := hasDerivAt_comp_sz_x q q' hq z.1 z.2
  have hq's := hasDerivAt_comp_sz_x q' q'' hq' z.1 z.2
  have h := ((hw.const_mul 2).mul hqs).add (((hx.const_mul 2).mul (hw.pow 2)).mul hq's)
  have h' : HasDerivAt (fun x : ℝ => 2 * wz (x, z.2) * q (sz (x, z.2)) +
      2 * (x : ℂ) * wz (x, z.2) ^ 2 * q' (sz (x, z.2)))
      (2 * q (sz z) + 8 * (z.1 : ℂ) * wz z * q' (sz z) + 2 * wz z ^ 2 * q' (sz z) +
        4 * (z.1 : ℂ) ^ 2 * wz z ^ 2 * q'' (sz z)) z.1 := by
    refine h.congr_deriv ?_
    simp only [Prod.mk.eta, Pi.mul_apply, Pi.pow_apply, Pi.add_apply]
    push_cast
    ring
  exact h'.deriv

theorem dydy_angF (hq : ∀ s, HasDerivAt q (q' s) s) (hq' : ∀ s, HasDerivAt q' (q'' s) s)
    (z : ℝ × ℝ) :
    B0093.dy (B0093.dy (angF q)) z =
      -2 * q (sz z) + 8 * Complex.I * (z.2 : ℂ) * wz z * q' (sz z) +
        2 * wz z ^ 2 * q' (sz z) + 4 * (z.2 : ℂ) ^ 2 * wz z ^ 2 * q'' (sz z) := by
  rw [dy_angF q q' hq]
  have hw := hasDerivAt_wz_y z.1 z.2
  have hy := hasDerivAt_ofReal z.2
  have hqs := hasDerivAt_comp_sz_y q q' hq z.1 z.2
  have hq's := hasDerivAt_comp_sz_y q' q'' hq' z.1 z.2
  have h := ((hw.const_mul (2 * Complex.I)).mul hqs).add
    (((hy.const_mul 2).mul (hw.pow 2)).mul hq's)
  have h' : HasDerivAt (fun y : ℝ => 2 * Complex.I * wz (z.1, y) * q (sz (z.1, y)) +
      2 * (y : ℂ) * wz (z.1, y) ^ 2 * q' (sz (z.1, y)))
      (-2 * q (sz z) + 8 * Complex.I * (z.2 : ℂ) * wz z * q' (sz z) +
        2 * wz z ^ 2 * q' (sz z) + 4 * (z.2 : ℂ) ^ 2 * wz z ^ 2 * q'' (sz z)) z.2 := by
    refine h.congr_deriv ?_
    simp only [Prod.mk.eta, Pi.mul_apply, Pi.pow_apply, Pi.add_apply]
    push_cast
    linear_combination (2 * q (sz z)) * Complex.I_sq
  exact h'.deriv

/-- **The operator `D` on angular-two functions** `w² q(|y|²)`:
`D F = w² (4 s q'' + (12 + s) q' + 3 q)`. -/
theorem gaussianOperator_angF (hq : ∀ s, HasDerivAt q (q' s) s)
    (hq' : ∀ s, HasDerivAt q' (q'' s) s) (z : ℝ × ℝ) :
    B0093.gaussianOperator (angF q) z =
      wz z ^ 2 * (4 * (sz z : ℂ) * q'' (sz z) + (12 + (sz z : ℂ)) * q' (sz z) + 3 * q (sz z)) := by
  rw [B0093.gaussianOperator, B0093.laplacian, dxdx_angF q q' q'' hq hq',
    dydy_angF q q' q'' hq hq', dx_angF q q' hq, dy_angF q q' hq]
  simp only [angF, Complex.real_smul]
  have hw : wz z = (z.1 : ℂ) + (z.2 : ℂ) * Complex.I := rfl
  have hs : (sz z : ℂ) = (z.1 : ℂ) ^ 2 + (z.2 : ℂ) ^ 2 := by simp [sz]
  rw [hs]
  push_cast
  rw [hw]
  ring

end Calculus

/-! ## The profiles `p(s) e^{-s/4}` -/

/-- `q_p(s) = p(s) e^{-s/4}`. -/
def qp (p : ℂ[X]) (s : ℝ) : ℂ := p.eval (s : ℂ) * (Real.exp (-(s / 4)) : ℂ)

theorem hasDerivAt_qp (p : ℂ[X]) (s : ℝ) :
    HasDerivAt (qp p) (qp (derivative p - (1 / 4 : ℂ) • p) s) s := by
  have h1 : HasDerivAt (fun s : ℝ => p.eval (s : ℂ)) ((derivative p).eval (s : ℂ)) s :=
    (p.hasDerivAt (s : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun s : ℝ => ((Real.exp (-(s / 4)) : ℝ) : ℂ))
      ((Real.exp (-(s / 4)) * (-(1 / 4)) : ℝ) : ℂ) s := by
    have h := (Real.hasDerivAt_exp (-(s / 4))).comp s
      (((hasDerivAt_id s).div_const 4).neg)
    exact h.ofReal_comp
  refine (h1.mul h2).congr_deriv ?_
  simp only [qp, eval_sub, eval_smul, smul_eq_mul]
  push_cast
  ring

theorem eval_lag (p : ℂ[X]) (x : ℂ) :
    (lag p).eval x = 4 * x * (derivative (derivative p)).eval x +
      (12 - x) * (derivative p).eval x := by
  simp only [lag_apply, eval_add, eval_mul, eval_sub, eval_X]
  norm_num

/-- The bracket `4 s q'' + (12 + s) q' + 3 q` for `q = q_p` is `q_{lag p}`. -/
theorem bracket_qp (p : ℂ[X]) (s : ℝ) :
    4 * (s : ℂ) * qp (derivative (derivative p - (1 / 4 : ℂ) • p) -
        (1 / 4 : ℂ) • (derivative p - (1 / 4 : ℂ) • p)) s +
      (12 + (s : ℂ)) * qp (derivative p - (1 / 4 : ℂ) • p) s + 3 * qp p s = qp (lag p) s := by
  simp only [qp, eval_lag, map_sub, map_smul, eval_sub, eval_smul, smul_eq_mul]
  ring

/-- The planar realization of the profile `r² p(r²) e^{-r²/4}` is `w² q_p(|y|²)`. -/
theorem angularTwoField_profFun (p : ℂ[X]) (z : ℝ × ℝ) :
    angularTwoField (profFun p) z = angF (qp p) z := by
  simp only [angularTwoField, profFun, angF, qp, gauss, polarCoord_apply]
  set ζ := Complex.equivRealProd.symm z with hζ
  have hζ' : ζ = wz z := by rw [hζ, Complex.equivRealProd_symm_apply]; rfl
  have hnorm : Real.sqrt (z.1 ^ 2 + z.2 ^ 2) = ‖ζ‖ := by
    rw [hζ', wz, Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    ring_nf
  have hsq : (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ 2 = sz z := Real.sq_sqrt (by positivity)
  have hpolar : ((Real.sqrt (z.1 ^ 2 + z.2 ^ 2) : ℝ) : ℂ) ^ 2 *
      Complex.exp (2 * Complex.I * (Complex.arg ζ : ℂ)) = wz z ^ 2 := by
    rw [← hζ', hnorm]
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I ζ]
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hcast : ((Real.sqrt (z.1 ^ 2 + z.2 ^ 2) : ℝ) : ℂ) ^ 2 = ((sz z : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hsq]
  rw [← hpolar, hcast, ← hsq]
  push_cast
  ring

/-- **`D` on the core.** For every polynomial `p`, the operator `D = Δ + ½ y·∇ + 2`
(`B0093.gaussianOperator`, tex line 723) maps the angular-two function
`r² p(r²) e^{-r²/4} e^{2iϑ}` to `r² (lag p)(r²) e^{-r²/4} e^{2iϑ}`, everywhere on `ℝ²`. -/
theorem gaussianOperator_angularTwoField_profFun (p : ℂ[X]) :
    B0093.gaussianOperator (angularTwoField (profFun p)) =
      angularTwoField (profFun (lag p)) := by
  have hF : angularTwoField (profFun p) = angF (qp p) := funext (angularTwoField_profFun p)
  funext z
  rw [hF, gaussianOperator_angF (qp p) _ _ (hasDerivAt_qp p) (hasDerivAt_qp _) z,
    bracket_qp, angularTwoField_profFun]
  rfl

end UnforcedLeray.B0094
