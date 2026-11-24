import UnforcedLeray.Lib.Gaussian.Kernel
import UnforcedLeray.Lib.Gaussian.Absorb
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Iterated-derivative bounds for the heat kernel on `ℝ^d` (INF22 G1, bypass BP3)


and §5 target G1; decision D14 (one generic-dimension Gaussian module, also serving INF04 T2 and
the Gaussian part of INF02 T5).

Route (BP3): `G_t = A · exp ∘ f` with `f(x) = -|x|²/(4t)`; every derivative of `exp` at `f(x)` has
norm `e^{f(x)}`, `‖Df(x)‖ = |x|/(2t)`, `‖D²f‖ ≤ 1/(2t)` and `D^k f = 0` for `k ≥ 3`, so Mathlib's
pointwise Faà di Bruno bound `norm_iteratedFDeriv_comp_le` gives
`‖D^n G_t(x)‖ ≤ n! G_t(x) ((|x|/√t + 1)/√t)^n`, and the polynomial factor is absorbed (G2).

Manuscript uses: Gaussian derivative bounds "‖D^j G_t‖ ≤ C_j t^{-(d+j)/2} e^{-|x|²/(8t)}" behind
B0163/B0164 (tex 2454–2467, the 1D case `d = 1`), B0181, B0423 (tex 7447–7477, kernel
`1_{t>0}∂_{ij}G_t`), B0722 (tex 466–492), the Oseen bounds via BP4 (tex 3.7–3.8), and
B0147/B0239/B0814 (tex 2217–2234, 4133–4147, 11888–11902), where "C_j" is unspecified.

Main results:
* `norm_iteratedFDeriv_gaussKernel_le` (G1):
  `‖D^n G_t(x)‖ ≤ C t^{-(d+n)/2} e^{-|x|²/(8t)}`, `C = C(d, n)`, for all `t > 0`, `x`;
* `norm_iteratedFDeriv_gaussKernel_le_parabolic` (INF02 T5, size and gradient bounds in the
  parabolic gauge): `‖D^n G_t(x)‖ ≤ C (t + |x|²)^{-(d+n)/2}`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open MeasureTheory Real
open scoped Nat

section LinearDerivs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A continuous linear map has vanishing derivatives of order `≥ 2`. -/
theorem iteratedFDeriv_clm_eq_zero (L : E →L[ℝ] F) (x : E) {k : ℕ} (hk : 2 ≤ k) :
    iteratedFDeriv ℝ k L x = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 2, by omega⟩
  rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv]
  have : fderiv ℝ L = fun _ => L := funext fun y => L.fderiv
  rw [this, iteratedFDeriv_succ_const]
  simp

end LinearDerivs

section NormSq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fderiv_normSq_eq_clm :
    fderiv ℝ (fun y : E => ‖y‖ ^ 2) = ⇑((2 : ℝ) • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)) := by
  funext y
  rw [fderiv_norm_sq_apply, ContinuousLinearMap.smul_apply, two_smul, two_smul]

theorem norm_innerSL_real_le : ‖(innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [innerSL_apply_norm, one_mul]

/-- First derivative of `|x|²`: norm `2|x|`. -/
theorem norm_iteratedFDeriv_one_normSq (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun y : E => ‖y‖ ^ 2) x‖ = 2 * ‖x‖ := by
  rw [norm_iteratedFDeriv_one, fderiv_norm_sq_apply, two_smul, ← two_smul ℝ, norm_smul,
    innerSL_apply_norm]
  norm_num

/-- Second derivative of `|x|²`: norm at most `2`. -/
theorem norm_iteratedFDeriv_two_normSq_le (x : E) :
    ‖iteratedFDeriv ℝ 2 (fun y : E => ‖y‖ ^ 2) x‖ ≤ 2 := by
  rw [← norm_iteratedFDeriv_fderiv, fderiv_normSq_eq_clm, norm_iteratedFDeriv_one,
    ContinuousLinearMap.fderiv, norm_smul]
  have := norm_innerSL_real_le (E := E)
  norm_num
  linarith

/-- Derivatives of order `≥ 3` of `|x|²` vanish. -/
theorem norm_iteratedFDeriv_normSq_eq_zero (x : E) {k : ℕ} (hk : 3 ≤ k) :
    ‖iteratedFDeriv ℝ k (fun y : E => ‖y‖ ^ 2) x‖ = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv, fderiv_normSq_eq_clm,
    iteratedFDeriv_clm_eq_zero _ _ (by omega), norm_zero]

end NormSq

/-- `‖D^i exp(y)‖ = e^y` for every order `i`. -/
theorem norm_iteratedFDeriv_exp (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_of_nonneg (Real.exp_pos y).le]

/-- `(u+1)^n e^{-u²/8} ≤ K_n` for `u ≥ 0`. -/
theorem add_one_pow_mul_exp_le (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 0 ≤ u → (u + 1) ^ n * Real.exp (-(1 / 8 * u ^ 2)) ≤ K := by
  obtain ⟨C, hC0, hC⟩ := rpow_mul_exp_neg_mul_sq_le (m := (n : ℝ)) (b := 1 / 8)
    (Nat.cast_nonneg n) (by norm_num)
  refine ⟨2 ^ n * (C + 1), by positivity, fun u hu => ?_⟩
  have h1 : (u + 1) ^ n ≤ 2 ^ n * (u ^ n + 1) := by
    have := add_pow_le hu zero_le_one n
    rw [one_pow] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
  have h2 : u ^ n * Real.exp (-(1 / 8 * u ^ 2)) ≤ C := by
    have := hC u hu; rwa [Real.rpow_natCast] at this
  have h3 : Real.exp (-(1 / 8 * u ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have he : 0 ≤ Real.exp (-(1 / 8 * u ^ 2)) := (Real.exp_pos _).le
  calc (u + 1) ^ n * Real.exp (-(1 / 8 * u ^ 2))
      ≤ 2 ^ n * (u ^ n + 1) * Real.exp (-(1 / 8 * u ^ 2)) := by gcongr
    _ = 2 ^ n * (u ^ n * Real.exp (-(1 / 8 * u ^ 2)) + Real.exp (-(1 / 8 * u ^ 2))) := by ring
    _ ≤ 2 ^ n * (C + 1) := by gcongr

/-- The Faà di Bruno step: `‖D^n G_t(x)‖ ≤ (4πt)^{-d/2} n! e^{-|x|²/(4t)} D^n` for any
`D ≥ |x|/(2t)` with `D² ≥ 1/(2t)`. -/
theorem norm_iteratedFDeriv_gaussKernel_le_aux {d : ℕ} (n : ℕ) {t : ℝ} (ht : 0 < t) (x : Euc d)
    {D : ℝ} (hD0 : 0 ≤ D) (hD1 : ‖x‖ / (2 * t) ≤ D) (hD2 : 1 / (2 * t) ≤ D ^ 2) :
    ‖iteratedFDeriv ℝ n (gaussKernel d t) x‖ ≤
      (4 * π * t) ^ (-(d : ℝ) / 2) * (n ! * Real.exp (-‖x‖ ^ 2 / (4 * t)) * D ^ n) := by
  set A := (4 * π * t) ^ (-(d : ℝ) / 2) with hA_def
  have hA : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  set f : Euc d → ℝ := fun y => -(4 * t)⁻¹ * ‖y‖ ^ 2 with hf_def
  have hf : ContDiff ℝ n f := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hG : gaussKernel d t = fun y => A • (Real.exp ∘ f) y := by
    funext y; rw [gaussKernel_eq_exp]; rfl
  have hEF : ContDiff ℝ n (Real.exp ∘ f) := Real.contDiff_exp.comp hf
  rw [hG, iteratedFDeriv_const_smul_apply' (hEF.contDiffAt), norm_smul,
    Real.norm_of_nonneg hA.le]
  refine mul_le_mul_of_nonneg_left ?_ hA.le
  have hfx : f x = -‖x‖ ^ 2 / (4 * t) := by simp only [hf_def]; ring
  rw [← hfx]
  refine norm_iteratedFDeriv_comp_le Real.contDiff_exp hf le_rfl x
    (fun i _ => (norm_iteratedFDeriv_exp i (f x)).le) ?_
  intro i hi1 _
  have hsmul : iteratedFDeriv ℝ i f x =
      (-(4 * t)⁻¹) • iteratedFDeriv ℝ i (fun y : Euc d => ‖y‖ ^ 2) x := by
    show iteratedFDeriv ℝ i (fun y : Euc d => (-(4 * t)⁻¹) • ‖y‖ ^ 2) x = _
    exact iteratedFDeriv_const_smul_apply' ((contDiff_norm_sq ℝ).contDiffAt)
  have hc : ‖(-(4 * t)⁻¹ : ℝ)‖ = (4 * t)⁻¹ := by
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
  rw [hsmul, norm_smul, hc]
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · rw [norm_iteratedFDeriv_one_normSq, pow_one]
    calc (4 * t)⁻¹ * (2 * ‖x‖) = ‖x‖ / (2 * t) := by field_simp; ring
      _ ≤ D := hD1
  · calc (4 * t)⁻¹ * ‖iteratedFDeriv ℝ 2 (fun y : Euc d => ‖y‖ ^ 2) x‖
        ≤ (4 * t)⁻¹ * 2 := by
          gcongr; exact norm_iteratedFDeriv_two_normSq_le x
      _ = 1 / (2 * t) := by field_simp; ring
      _ ≤ D ^ 2 := hD2
  · rw [norm_iteratedFDeriv_normSq_eq_zero x h3, mul_zero]
    positivity

/-- **INF22 G1.** Gaussian iterated-derivative bounds in dimension `d`:
`‖D^n G_t(x)‖ ≤ C t^{-(d+n)/2} e^{-|x|²/(8t)}` for all `t > 0` and `x ∈ ℝ^d`, with `C = C(d,n)`.
(The scoping note's displayed statement writes `t ^ (-((d + n : ℝ) / 2))`.) -/
theorem norm_iteratedFDeriv_gaussKernel_le (d n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {t : ℝ}, 0 < t → ∀ x : Euc d, ‖iteratedFDeriv ℝ n (gaussKernel d t) x‖ ≤
      C * t ^ (-(((d : ℝ) + n) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * t)) := by
  obtain ⟨K, hK0, hK⟩ := add_one_pow_mul_exp_le n
  refine ⟨(4 * π) ^ (-(d : ℝ) / 2) * n ! * K, by positivity, fun {t} ht x => ?_⟩
  set σ := Real.sqrt t with hσ_def
  have hσ : 0 < σ := Real.sqrt_pos.2 ht
  have hσt : σ ^ 2 = t := Real.sq_sqrt ht.le
  set u := ‖x‖ / σ with hu_def
  have hu : 0 ≤ u := div_nonneg (norm_nonneg _) hσ.le
  have hxu : ‖x‖ = σ * u := by rw [hu_def]; field_simp
  set D := (u + 1) / σ with hD_def
  have hD0 : 0 ≤ D := by positivity
  have hD1 : ‖x‖ / (2 * t) ≤ D := by
    rw [hxu, ← hσt, hD_def, div_le_div_iff₀ (by positivity) hσ]
    nlinarith [sq_nonneg σ, mul_pos hσ hσ]
  have hD2 : 1 / (2 * t) ≤ D ^ 2 := by
    rw [← hσt, hD_def, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg u, sq_nonneg σ, mul_pos hσ hσ]
  refine (norm_iteratedFDeriv_gaussKernel_le_aux n ht x hD0 hD1 hD2).trans ?_
  -- algebra: split the Gaussian and the powers of `t`
  have hsplit : Real.exp (-‖x‖ ^ 2 / (4 * t)) =
      Real.exp (-(1 / 8 * u ^ 2)) * Real.exp (-‖x‖ ^ 2 / (8 * t)) := by
    rw [← Real.exp_add, hxu, ← hσt]; congr 1; field_simp; ring
  have hDn : D ^ n = (u + 1) ^ n * (σ ^ n)⁻¹ := by rw [hD_def, div_pow, div_eq_mul_inv]
  have hσn : (σ ^ n)⁻¹ = t ^ (-((n : ℝ) / 2)) := by
    rw [hσ_def, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le,
      Real.rpow_neg ht.le]
    congr 2; ring
  have hAt : (4 * π * t) ^ (-(d : ℝ) / 2) * t ^ (-((n : ℝ) / 2)) =
      (4 * π) ^ (-(d : ℝ) / 2) * t ^ (-(((d : ℝ) + n) / 2)) := by
    rw [Real.mul_rpow (by positivity) ht.le, mul_assoc, ← Real.rpow_add ht]
    congr 3; ring
  rw [hsplit, hDn, hσn]
  have hk := hK u hu
  have hE : 0 < Real.exp (-‖x‖ ^ 2 / (8 * t)) := Real.exp_pos _
  calc (4 * π * t) ^ (-(d : ℝ) / 2) * (n ! * (Real.exp (-(1 / 8 * u ^ 2)) *
        Real.exp (-‖x‖ ^ 2 / (8 * t))) * ((u + 1) ^ n * t ^ (-((n : ℝ) / 2))))
      = ((4 * π * t) ^ (-(d : ℝ) / 2) * t ^ (-((n : ℝ) / 2))) * n ! *
          ((u + 1) ^ n * Real.exp (-(1 / 8 * u ^ 2))) * Real.exp (-‖x‖ ^ 2 / (8 * t)) := by
        ring
    _ ≤ ((4 * π * t) ^ (-(d : ℝ) / 2) * t ^ (-((n : ℝ) / 2))) * n ! * K *
          Real.exp (-‖x‖ ^ 2 / (8 * t)) := by gcongr
    _ = (4 * π) ^ (-(d : ℝ) / 2) * n ! * K * t ^ (-(((d : ℝ) + n) / 2)) *
          Real.exp (-‖x‖ ^ 2 / (8 * t)) := by rw [hAt]; ring

/-- Parabolic form of G2: `t^{-m/2} e^{-r²/(8t)} ≤ C (t + r²)^{-m/2}` for `t > 0`, `m ≥ 0`. -/
theorem rpow_mul_exp_le_parabolic {m : ℝ} (hm : 0 ≤ m) : ∃ C : ℝ, 0 < C ∧
    ∀ t r : ℝ, 0 < t → t ^ (-m / 2) * Real.exp (-r ^ 2 / (8 * t)) ≤
      C * (t + r ^ 2) ^ (-m / 2) := by
  obtain ⟨C₀, hC₀, hC⟩ := rpow_mul_exp_neg_le (p := m / 2) (by positivity)
  refine ⟨8 ^ (m / 2) * Real.exp (1 / 8) * C₀, by positivity, fun t r ht => ?_⟩
  set w := r ^ 2 / t with hw_def
  have hw : 0 ≤ w := by positivity
  set v := (1 + w) / 8 with hv_def
  have hv : 0 ≤ v := by positivity
  have htr : t + r ^ 2 = t * (8 * v) := by rw [hv_def, hw_def]; field_simp
  have hexp : Real.exp (-r ^ 2 / (8 * t)) = Real.exp (1 / 8) * Real.exp (-v) := by
    rw [← Real.exp_add]; congr 1; rw [hv_def, hw_def]; field_simp; ring
  rw [htr, Real.mul_rpow ht.le (by positivity), Real.mul_rpow (by norm_num) hv, hexp]
  have hvpos : 0 < v := by rw [hv_def]; positivity
  have h8 : (8 : ℝ) ^ (m / 2) * 8 ^ (-m / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp [neg_div]
  have key : Real.exp (-v) ≤ C₀ * v ^ (-m / 2) := by
    have h := hC v hv
    have hvm : 0 < v ^ (m / 2) := Real.rpow_pos_of_pos hvpos _
    rw [neg_div, Real.rpow_neg hv, ← div_eq_mul_inv, le_div_iff₀ hvm]
    linarith [mul_comm (v ^ (m / 2)) (Real.exp (-v))]
  have ht' : 0 < t ^ (-m / 2) := Real.rpow_pos_of_pos ht _
  calc t ^ (-m / 2) * (Real.exp (1 / 8) * Real.exp (-v))
      ≤ t ^ (-m / 2) * (Real.exp (1 / 8) * (C₀ * v ^ (-m / 2))) := by gcongr
    _ = 8 ^ (m / 2) * Real.exp (1 / 8) * C₀ * (t ^ (-m / 2) * (8 ^ (-m / 2) * v ^ (-m / 2))) := by
        calc _ = ((8 : ℝ) ^ (m / 2) * 8 ^ (-m / 2)) *
              (t ^ (-m / 2) * (Real.exp (1 / 8) * (C₀ * v ^ (-m / 2)))) := by rw [h8, one_mul]
          _ = _ := by ring

/-- **INF02 T5 (Gaussian part), size and gradient bounds in the parabolic gauge.**
`‖D^n G_t(x)‖ ≤ C (t + |x|²)^{-(d+n)/2}` for all `t > 0`, `x ∈ ℝ^d`. With `n = 2` this is the
size bound of the causal kernel `1_{t>0}∂_{ij}G_t` (tex 7447–7477, B0423), with `n = 3` its
gradient bound, homogeneous of parabolic dimension `d + 2`. -/
theorem norm_iteratedFDeriv_gaussKernel_le_parabolic (d n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {t : ℝ}, 0 < t → ∀ x : Euc d, ‖iteratedFDeriv ℝ n (gaussKernel d t) x‖ ≤
      C * (t + ‖x‖ ^ 2) ^ (-(((d : ℝ) + n) / 2)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := norm_iteratedFDeriv_gaussKernel_le d n
  obtain ⟨C₂, hC₂, h₂⟩ := rpow_mul_exp_le_parabolic (m := (d : ℝ) + n) (by positivity)
  refine ⟨C₁ * C₂, by positivity, fun {t} ht x => (h₁ ht x).trans ?_⟩
  have := h₂ t ‖x‖ ht
  rw [neg_div] at this
  calc C₁ * t ^ (-(((d : ℝ) + n) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * t))
      = C₁ * (t ^ (-(((d : ℝ) + n) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * t))) := by ring
    _ ≤ C₁ * (C₂ * (t + ‖x‖ ^ 2) ^ (-(((d : ℝ) + n) / 2))) := by gcongr
    _ = C₁ * C₂ * (t + ‖x‖ ^ 2) ^ (-(((d : ℝ) + n) / 2)) := by ring

end UnforcedLeray.Gaussian
