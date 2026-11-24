import UnforcedLeray.Units.B0010
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# B0094 helper: Gaussian-polynomial profiles in `X_G` and the Laguerre operator

Blueprint unit B0094 (`eq:st18-t00068`, `paper/main.tex` lines 1503--1515).

The angular-two Hermite levels of tex lines 1504--1510 are spanned by the profiles
`r² p(r²) e^{-r²/4}` with `p` a polynomial (in the oscillator picture of B0093 these are
`U_G⁻¹` of `(x+iy)² p(|y|²) e^{-|y|²/8}`). This file sets up:
* `profFun p r = r² p(r²) e^{-r²/4}` and `prof : ℂ[X] →ₗ[ℂ] XG` (`XG` from B0010);
* `prof_injective`;
* `lag p = 4 X p'' + (12 - X) p'`: on these profiles the operator `D = Δ + ½ y·∇ + 2`
  acts as `profFun p ↦ profFun (lag p)` (the planar computation is in `Planar.lean`);
  in the variable `x = r²/4` this is the Laguerre operator `x ∂² + (3 - x) ∂`;
* the Gram matrix `⟪prof Xᵃ, prof Xᵇ⟫ = 4π · 2·4^{a+b+2}(a+b+2)!` and the symmetry
  `⟪prof (lag p), prof q⟫ = ⟪prof p, prof (lag q)⟫`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Polynomial
open scoped ComplexConjugate Real InnerProductSpace Nat

namespace UnforcedLeray.B0094

open UnforcedLeray.B0010

/-- `e^{-r²/4}` as a complex number. -/
def gauss (r : ℝ) : ℂ := (Real.exp (-(r ^ 2 / 4)) : ℂ)

/-- The profile `r² p(r²) e^{-r²/4}`. -/
def profFun (p : ℂ[X]) (r : ℝ) : ℂ := (r : ℂ) ^ 2 * p.eval ((r : ℂ) ^ 2) * gauss r

/-- The monomial profile `r^{2+2k} e^{-r²/4}` (real valued). -/
def monoReal (k : ℕ) (r : ℝ) : ℝ := r ^ (2 + 2 * k) * Real.exp (-(r ^ 2 / 4))

theorem profFun_X_pow (k : ℕ) (r : ℝ) : profFun (X ^ k) r = (monoReal k r : ℂ) := by
  simp only [profFun, eval_pow, eval_X, gauss, monoReal]
  push_cast
  ring

theorem profFun_add (p q : ℂ[X]) : profFun (p + q) = profFun p + profFun q := by
  funext r
  simp only [profFun, eval_add, Pi.add_apply]
  ring

theorem profFun_smul (c : ℂ) (p : ℂ[X]) : profFun (c • p) = c • profFun p := by
  funext r
  simp only [profFun, eval_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_profFun (p : ℂ[X]) : Continuous (profFun p) := by
  unfold profFun gauss
  fun_prop

/-- The weight `G(r)⁻¹ r = 4π e^{r²/4} r`. -/
theorem weight_eq (r : ℝ) : (radialGaussianWeight r)⁻¹ * r = 4 * π * Real.exp (r ^ 2 / 4) * r := by
  rw [radialGaussianWeight_inv]

theorem exp_quarter_mul (r : ℝ) : Real.exp (-(r ^ 2 / 4)) * Real.exp (r ^ 2 / 4) = 1 := by
  rw [← Real.exp_add]
  simp

/-- `∫₀^∞ r^{2m+1} e^{-r²/4} dr = 2·4^m·m!`. -/
def gaussMoment (m : ℕ) : ℝ := 2 * 4 ^ m * (m ! : ℝ)

theorem gaussMoment_succ (m : ℕ) : gaussMoment (m + 1) = 4 * (m + 1) * gaussMoment m := by
  simp only [gaussMoment, Nat.factorial_succ, pow_succ]
  push_cast
  ring

theorem integrableOn_pow_mul_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => r ^ n * Real.exp (-b * r ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq hb (s := (n : ℝ)) (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast]

theorem integral_moment (m : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ (2 * m + 1) * Real.exp (-(r ^ 2 / 4)) = gaussMoment m := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((2 * m + 1 : ℕ) : ℝ))
    (b := 1 / 4) two_pos (by have : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
    (by norm_num)
  have hcongr : ∫ r in Ioi (0 : ℝ), r ^ (2 * m + 1) * Real.exp (-(r ^ 2 / 4)) =
      ∫ x in Ioi (0 : ℝ), x ^ ((2 * m + 1 : ℕ) : ℝ) * Real.exp (-(1 / 4) * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    simp only [Real.rpow_natCast, Real.rpow_two]
    ring_nf
  rw [hcongr, h]
  have h1 : (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = ((m : ℕ) : ℝ) + 1 := by push_cast; ring
  have h2 : -(((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = -(((m + 1 : ℕ) : ℝ)) := by push_cast; ring
  rw [h1, h2, Real.Gamma_nat_eq_factorial, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [one_div, inv_pow, inv_inv, pow_succ]
  simp only [gaussMoment]
  ring

/-- The integrand of the `X_G` norm of `profFun (X^k)`. -/
theorem norm_sq_monoReal_weight (k : ℕ) {r : ℝ} (hr : 0 < r) :
    ‖profFun (X ^ k) r‖ ^ 2 * ((radialGaussianWeight r)⁻¹ * r) =
      4 * π * (r ^ (4 * k + 5) * Real.exp (-(1 / 4) * r ^ 2)) := by
  rw [profFun_X_pow, Complex.norm_real, Real.norm_of_nonneg (by unfold monoReal; positivity),
    weight_eq, monoReal]
  have := exp_quarter_mul r
  have e2 : Real.exp (-(1 / 4) * r ^ 2) = Real.exp (-(r ^ 2 / 4)) := by ring_nf
  rw [e2]
  linear_combination (4 * π * r ^ (4 * k + 5) * Real.exp (-(r ^ 2 / 4))) * this

theorem memLp_profFun_X_pow (k : ℕ) : MemLp (profFun (X ^ k)) 2 xGMeasure := by
  have hm : AEStronglyMeasurable (profFun (X ^ k)) (volume.restrict (Ioi 0)) :=
    (continuous_profFun _).aestronglyMeasurable
  rw [memLp_iff_integrableOn hm]
  have h : IntegrableOn (fun r : ℝ => 4 * π * (r ^ (4 * k + 5) * Real.exp (-(1 / 4) * r ^ 2)))
      (Ioi 0) := (integrableOn_pow_mul_exp (4 * k + 5) (b := 1 / 4) (by norm_num)).const_mul _
  refine h.congr_fun (fun r hr => (norm_sq_monoReal_weight k hr).symm) measurableSet_Ioi

theorem memLp_profFun (p : ℂ[X]) : MemLp (profFun p) 2 xGMeasure := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [profFun_add]; exact hp.add hq
  | monomial k c =>
    rw [← smul_X_eq_monomial, profFun_smul]
    exact (memLp_profFun_X_pow k).const_smul c

/-- The profiles `r² p(r²) e^{-r²/4}` as elements of `X_G`. -/
def prof : ℂ[X] →ₗ[ℂ] XG where
  toFun p := (memLp_profFun p).toLp _
  map_add' p q := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun r => congrFun (profFun_add p q) r)
  map_smul' c p := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _
      (Filter.Eventually.of_forall fun r => congrFun (profFun_smul c p) r)

theorem coeFn_prof (p : ℂ[X]) : (prof p : ℝ → ℂ) =ᵐ[xGMeasure] profFun p :=
  (memLp_profFun p).coeFn_toLp

/-- The inner product of two profiles. -/
theorem inner_prof (p q : ℂ[X]) :
    ⟪prof p, prof q⟫_ℂ =
      ∫ r in Ioi 0, profFun q r * conj (profFun p r) *
        (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ) := by
  rw [← pairing_eq_inner]
  exact pairing_toLp (memLp_profFun q) (memLp_profFun p)

/-- The Gram matrix of the monomial profiles. -/
theorem inner_prof_X_pow (a b : ℕ) :
    ⟪prof (X ^ a), prof (X ^ b)⟫_ℂ = ((4 * π * gaussMoment (a + b + 2) : ℝ) : ℂ) := by
  rw [inner_prof, ← integral_moment, ← integral_const_mul]
  have : ∀ r ∈ Ioi (0 : ℝ), profFun (X ^ b) r * conj (profFun (X ^ a) r) *
      (((radialGaussianWeight r)⁻¹ * r : ℝ) : ℂ) =
      ((4 * π * (r ^ (2 * (a + b + 2) + 1) * Real.exp (-(r ^ 2 / 4))) : ℝ) : ℂ) := by
    intro r _
    rw [profFun_X_pow, profFun_X_pow, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, weight_eq, monoReal, monoReal]
    congr 1
    linear_combination (4 * π * r ^ (2 * (a + b + 2) + 1) * Real.exp (-(r ^ 2 / 4))) *
      exp_quarter_mul r
  rw [setIntegral_congr_fun measurableSet_Ioi this]
  exact integral_ofReal

theorem norm_prof_X_pow_pos (a : ℕ) : prof (X ^ a) ≠ 0 := by
  intro h
  have := inner_prof_X_pow a a
  rw [h, inner_zero_left] at this
  have hpos : 0 < 4 * π * gaussMoment (a + a + 2) := by unfold gaussMoment; positivity
  have := congrArg Complex.re this
  simp only [Complex.zero_re, Complex.ofReal_re] at this
  linarith

/-! ## Injectivity -/

theorem prof_injective : Function.Injective prof := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  have h1 : profFun p =ᵐ[xGMeasure] 0 := by
    have := coeFn_prof p
    rw [hp] at this
    exact this.symm.trans (Lp.coeFn_zero _ _ _)
  rw [Filter.EventuallyEq, xGMeasure,
    ae_withDensity_iff measurable_xGDensity.coe_nnreal_ennreal] at h1
  have h2 : profFun p =ᵐ[volume.restrict (Ioi 0)] 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    rw [ae_restrict_iff' measurableSet_Ioi] at h1
    filter_upwards [h1] with r hr hr0
    refine hr hr0 ?_
    rw [ne_eq, ENNReal.coe_eq_zero, ← NNReal.coe_eq_zero, coe_xGDensity hr0]
    exact (mul_pos (inv_pos.2 (radialGaussianWeight_pos r)) hr0).ne'
  have h3 := Measure.eqOn_open_of_ae_eq h2 isOpen_Ioi (continuous_profFun p).continuousOn
    continuousOn_const
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono ?_ ((Set.Ioi_infinite (0 : ℝ)).image Complex.ofReal_injective.injOn)
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (0 : ℝ) < s := hs
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
  have := h3 hr
  simp only [profFun, Pi.zero_apply, gauss, mul_eq_zero, pow_eq_zero_iff, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, Complex.ofReal_eq_zero, Real.exp_ne_zero,
    or_false] at this
  rcases this with h | h
  · exact absurd h hr.ne'
  · rw [← Complex.ofReal_pow, Real.sq_sqrt hs'.le] at h
    exact h

/-! ## The Laguerre operator -/

/-- `lag p = 4 X p'' + (12 - X) p'`: the action of `D = Δ + ½ y·∇ + 2` on the profile
`r² p(r²) e^{-r²/4}` (see `Planar.lean`). -/
def lag : ℂ[X] →ₗ[ℂ] ℂ[X] where
  toFun p := 4 * X * derivative (derivative p) + (12 - X) * derivative p
  map_add' p q := by simp only [map_add]; ring
  map_smul' c p := by
    simp only [RingHom.id_apply, smul_eq_C_mul, derivative_C_mul]
    ring

theorem lag_apply (p : ℂ[X]) :
    lag p = 4 * X * derivative (derivative p) + (12 - X) * derivative p := rfl

theorem lag_X_pow (a : ℕ) :
    lag (X ^ a) = ((4 * a * (a + 2) : ℕ) : ℂ) • X ^ (a - 1) - (a : ℂ) • X ^ a := by
  rcases a with _ | _ | n
  · simp [lag_apply]
  · simp only [zero_add, pow_one, lag_apply, derivative_X, derivative_one, mul_zero, mul_one,
      Nat.sub_self, pow_zero]
    simp only [smul_eq_C_mul]
    push_cast
    simp only [map_ofNat, map_one]
    ring
  · simp only [lag_apply, derivative_X_pow, derivative_mul, derivative_C, zero_mul, zero_add,
      smul_eq_C_mul]
    simp only [Nat.add_sub_cancel, show n + 1 + 1 - 1 = n + 1 by omega,
      show n + 1 - 1 = n by omega]
    push_cast
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one]
    ring

/-- **Symmetry** of `D` on the Gaussian-polynomial profiles (Gram-matrix identity). -/
theorem inner_lag_X_pow (a b : ℕ) :
    ⟪prof (lag (X ^ a)), prof (X ^ b)⟫_ℂ = ⟪prof (X ^ a), prof (lag (X ^ b))⟫_ℂ := by
  rw [lag_X_pow, lag_X_pow]
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, inner_prof_X_pow, Complex.conj_natCast]
  rcases a with _ | a <;> rcases b with _ | b
  · simp
  · rw [show b + 1 + 2 = (b + 2) + 1 by omega, gaussMoment_succ]
    push_cast
    ring
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring_nf
    rw [show 3 + a = (2 + a) + 1 by ring, gaussMoment_succ]
    push_cast
    ring
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring_nf
    rw [show 4 + a + b = (3 + a + b) + 1 by ring, gaussMoment_succ]
    push_cast
    ring

theorem inner_lag_symm (p q : ℂ[X]) :
    ⟪prof (lag p), prof q⟫_ℂ = ⟪prof p, prof (lag q)⟫_ℂ := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | monomial a c =>
    rw [← smul_X_eq_monomial]
    simp only [map_smul, inner_smul_left]
    congr 1
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | monomial b d =>
      rw [← smul_X_eq_monomial]
      simp only [map_smul, inner_smul_right]
      rw [inner_lag_X_pow]

end UnforcedLeray.B0094
