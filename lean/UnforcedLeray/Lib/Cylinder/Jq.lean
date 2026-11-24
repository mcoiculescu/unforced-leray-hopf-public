import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The periodic primitive `J_q = ∂_q⁻¹` on zero-mean functions (INF13, target CY04)


§5 CY04 (`Jq`, `norm_Jq_le`).

`paper/main.tex` lines 9077-9085 (unit B0566) and 12246-12260 (unit B0828): "let
`J_q = ∂_q⁻¹` on the zero-mean periodic functions; `‖J_q‖_{2→2} ≤ c/π`."

`J_q` acts on `L²` of the circle `ℝ/cℤ`, realised as `Lp ℂ 2 haarAddCircle` (the phase space
convention of decision D2).  It is the Fourier multiplier with symbol `c / (2πin)` on the modes
`n ≠ 0` and `0` on the mean mode (`jqSymbol`).  The operator norm does not depend on the
normalisation of the measure, so `‖Jq c‖ ≤ c/(2π)` (`norm_Jq_le`) is the bound for
`L²(0, c; dq)`; the manuscript's `c/π` follows (`norm_Jq_le_div_pi`).

That `Jq c` is `∂_q⁻¹` on zero-mean functions is proved in both directions:
* `fourierCoeff_Jq_mul`: `(2πin/c) · (Jq f)^(n) = f^(n)` for `n ≠ 0`, i.e. the distributional
  derivative of `Jq f` is `f - mean f`; `Jq_mem_zeroMeanL2`: `Jq f` has mean zero;
* `Jq_perLp_deriv`: for a `C¹`, `c`-periodic `F : ℝ → ℂ` with `∫₀^c F = 0`,
  `Jq (F') = F` (`perLp` is the class of a continuous periodic function on the circle).

Main declarations: `jqSymbol`, `lpMul`, `L2circ`, `Jq`, `zeroMeanL2`, `JqZ`, `perLp`,
`fourierCoeff_Jq`, `norm_Jq_le`, `norm_Jq_le_div_pi`, `norm_JqZ_le`, `Jq_perLp_deriv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Complex
open scoped ENNReal

namespace UnforcedLeray.Cyl

/-! ### Bounded diagonal multipliers on `ℓ²(ℤ)` -/

section Multiplier

variable (m : ℤ → ℂ) {M : ℝ}

theorem memℓp_mul (hm : ∀ n, ‖m n‖ ≤ M) (a : lp (fun _ : ℤ => ℂ) 2) :
    Memℓp (fun n => m n * a n) 2 := by
  apply memℓp_gen
  have hs := (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs ⊢
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hs.mul_left (M ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hm n) 2) (by positivity)

/-- The diagonal multiplier `(a_n) ↦ (m_n a_n)` on `ℓ²(ℤ, ℂ)`, for a bounded symbol. -/
def lpMul (hM : 0 ≤ M) (hm : ∀ n, ‖m n‖ ≤ M) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨fun n => m n * a n, memℓp_mul m hm a⟩
      map_add' := fun a b => lp.ext <| funext fun n => by
        show m n * (a + b) n = m n * a n + m n * b n
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun r a => lp.ext <| funext fun n => by
        show m n * (r • a) n = r * (m n * a n)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    M (fun a => by
      refine lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg hM (norm_nonneg a)) ?_
      have hs := (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      have hs' := (memℓp_mul m hm a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs hs' ⊢
      calc ∑' n, ‖m n * a n‖ ^ 2 ≤ ∑' n, M ^ 2 * ‖a n‖ ^ 2 := by
            refine hs'.tsum_le_tsum (fun n => ?_) (hs.mul_left _)
            rw [norm_mul, mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hm n) 2)
              (by positivity)
        _ = (M * ‖a‖) ^ 2 := by
            rw [tsum_mul_left, mul_pow]
            congr 1
            have := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a
            simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
            exact this.symm)

theorem lpMul_apply (hM : 0 ≤ M) (hm : ∀ n, ‖m n‖ ≤ M) (a : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    lpMul m hM hm a n = m n * a n := rfl

theorem norm_lpMul_le (hM : 0 ≤ M) (hm : ∀ n, ‖m n‖ ≤ M) : ‖lpMul m hM hm‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM _

end Multiplier

/-! ### The symbol of `∂_q⁻¹` -/

/-- The Fourier symbol of `∂_q⁻¹` on `c`-periodic functions: `c / (2πin)` for `n ≠ 0`, and `0`
on the mean mode. -/
def jqSymbol (c : ℝ) (n : ℤ) : ℂ := if n = 0 then 0 else (c : ℂ) / (2 * π * I * n)

theorem jqSymbol_zero (c : ℝ) : jqSymbol c 0 = 0 := by simp [jqSymbol]

theorem jqSymbol_of_ne {c : ℝ} {n : ℤ} (hn : n ≠ 0) :
    jqSymbol c n = (c : ℂ) / (2 * π * I * n) := by simp [jqSymbol, hn]

theorem norm_jqSymbol_le {c : ℝ} (hc : 0 ≤ c) (n : ℤ) : ‖jqSymbol c n‖ ≤ c / (2 * π) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [jqSymbol_zero, norm_zero]; positivity
  · rw [jqSymbol_of_ne hn, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_I, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hc, abs_of_pos Real.pi_pos, mul_one]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    exact div_le_div_of_nonneg_left hc (by positivity) (le_mul_of_one_le_right (by positivity) h1)

theorem jqSymbol_mul {c : ℝ} (hc : c ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    (2 * π * I * n / c) * jqSymbol c n = 1 := by
  rw [jqSymbol_of_ne hn]
  have : (2 * π * I * n : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, hn, Complex.I_ne_zero]
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  field_simp

/-! ### The operator -/

section Operator

variable (c : ℝ) [hc : Fact (0 < c)]

/-- `L²` of the circle `ℝ / cℤ` with normalised Haar measure. -/
abbrev L2circ := Lp ℂ 2 (AddCircle.haarAddCircle (T := c))

/-- `J_q = ∂_q⁻¹` on zero-mean `c`-periodic `L²` functions, extended by `0` on the constants
(B0566, tex 9077-9085; B0828, tex 12246-12260). -/
def Jq : L2circ c →L[ℂ] L2circ c :=
  ((fourierBasis (T := c)).repr.symm.toContinuousLinearEquiv :
      lp (fun _ : ℤ => ℂ) 2 →L[ℂ] L2circ c).comp
    ((lpMul (jqSymbol c) (by have := hc.out; positivity) (norm_jqSymbol_le hc.out.le)).comp
      ((fourierBasis (T := c)).repr.toContinuousLinearEquiv :
        L2circ c →L[ℂ] lp (fun _ : ℤ => ℂ) 2))

variable {c}

theorem repr_Jq (f : L2circ c) (n : ℤ) :
    (fourierBasis (T := c)).repr (Jq c f) n = jqSymbol c n * (fourierBasis (T := c)).repr f n := by
  simp [Jq, lpMul_apply]

/-- `J_q` is the Fourier multiplier `jqSymbol`. -/
theorem fourierCoeff_Jq (f : L2circ c) (n : ℤ) :
    fourierCoeff (Jq c f) n = jqSymbol c n * fourierCoeff f n := by
  rw [← fourierBasis_repr, ← fourierBasis_repr, repr_Jq]

/-- `∂_q J_q f = f` on the modes `n ≠ 0`: `(2πin/c) (J_q f)^(n) = f^(n)`. -/
theorem fourierCoeff_Jq_mul (f : L2circ c) {n : ℤ} (hn : n ≠ 0) :
    (2 * π * I * n / c) * fourierCoeff (Jq c f) n = fourierCoeff f n := by
  rw [fourierCoeff_Jq, ← mul_assoc, jqSymbol_mul hc.out.ne' hn, one_mul]

/-- **The bound on `J_q`** (CY04 `norm_Jq_le`): `‖J_q‖_{2→2} ≤ c/(2π)`. -/
theorem norm_Jq_le : ‖Jq c‖ ≤ c / (2 * π) := by
  have hM : 0 ≤ c / (2 * π) := by have := hc.out; positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun f => ?_
  calc ‖Jq c f‖ = ‖(fourierBasis (T := c)).repr (Jq c f)‖ :=
        ((fourierBasis (T := c)).repr.norm_map _).symm
    _ = ‖lpMul (jqSymbol c) hM (norm_jqSymbol_le hc.out.le)
          ((fourierBasis (T := c)).repr f)‖ := by simp [Jq]
    _ ≤ c / (2 * π) * ‖(fourierBasis (T := c)).repr f‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_lpMul_le _ _ _) (norm_nonneg _))
    _ = c / (2 * π) * ‖f‖ := by rw [LinearIsometryEquiv.norm_map]

/-- The manuscript's form of the bound (B0566, B0828): `‖J_q‖_{2→2} ≤ c/π`. -/
theorem norm_Jq_le_div_pi : ‖Jq c‖ ≤ c / π := by
  refine norm_Jq_le.trans ?_
  have := hc.out
  exact div_le_div_of_nonneg_left this.le Real.pi_pos (by linarith [Real.pi_pos])

/-! ### Zero-mean functions -/

variable (c) in
/-- The zero-mean subspace of `L²(ℝ/cℤ)`. -/
def zeroMeanL2 : Submodule ℂ (L2circ c) where
  carrier := {f | fourierCoeff f 0 = 0}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← fourierBasis_repr] at *
    rw [map_add, lp.coeFn_add, Pi.add_apply, hf, hg, add_zero]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, ← fourierBasis_repr, map_zero]
    rfl
  smul_mem' r f hf := by
    simp only [Set.mem_ofPred_eq, ← fourierBasis_repr] at *
    rw [map_smul, lp.coeFn_smul, Pi.smul_apply, hf, smul_zero]

theorem mem_zeroMeanL2 (f : L2circ c) : f ∈ zeroMeanL2 c ↔ fourierCoeff f 0 = 0 := Iff.rfl

theorem Jq_mem_zeroMeanL2 (f : L2circ c) : Jq c f ∈ zeroMeanL2 c := by
  rw [mem_zeroMeanL2, fourierCoeff_Jq, jqSymbol_zero, zero_mul]

variable (c) in
/-- `J_q` as an operator on the zero-mean subspace. -/
def JqZ : zeroMeanL2 c →L[ℂ] zeroMeanL2 c :=
  ((Jq c).comp (zeroMeanL2 c).subtypeL).codRestrict (zeroMeanL2 c) fun _ => Jq_mem_zeroMeanL2 _

theorem JqZ_apply (f : zeroMeanL2 c) : (JqZ c f : L2circ c) = Jq c f := rfl

/-- `‖J_q‖ ≤ c/(2π)` on the zero-mean subspace. -/
theorem norm_JqZ_le : ‖JqZ c‖ ≤ c / (2 * π) := by
  have hM : 0 ≤ c / (2 * π) := by have := hc.out; positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun f => ?_
  rw [← Submodule.norm_coe, JqZ_apply, ← Submodule.norm_coe f]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right norm_Jq_le (norm_nonneg _))

/-! ### `J_q ∂_q F = F` for smooth zero-mean periodic `F` -/

variable (c) in
/-- The `L²(ℝ/cℤ)` class of a continuous `c`-periodic function `G : ℝ → ℂ`. -/
def perLp (G : ℝ → ℂ) (hG : Continuous G) (hper : Function.Periodic G c) : L2circ c :=
  ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ
    ⟨AddCircle.liftIco c 0 G, AddCircle.liftIco_continuous (by simpa using (hper 0).symm)
      hG.continuousOn⟩

theorem fourierCoeff_perLp (G : ℝ → ℂ) (hG : Continuous G) (hper : Function.Periodic G c)
    (n : ℤ) :
    fourierCoeff (perLp c G hG hper) n =
      fourierCoeffOn (lt_add_of_pos_right 0 hc.out) G n := by
  rw [perLp, fourierCoeff_toLp]
  exact fourierCoeff_liftIco_eq G n

omit hc in
theorem periodic_deriv {F : ℝ → ℂ} (hper : Function.Periodic F c) :
    Function.Periodic (deriv F) c := fun x => by
  rw [← deriv_comp_add_const (f := F) (a := c)]
  congr 1
  funext y
  exact hper y

/-- `J_q (∂_q F) = F` for a `C¹`, `c`-periodic, zero-mean `F` (CY04): `J_q` is the inverse of
`∂_q` on zero-mean periodic functions. -/
theorem Jq_perLp_deriv {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F) (hper : Function.Periodic F c)
    (hmean : ∫ x in (0 : ℝ)..c, F x = 0) :
    Jq c (perLp c (deriv F) (hF.continuous_deriv le_rfl) (periodic_deriv hper)) =
      perLp c F hF.continuous hper := by
  apply (fourierBasis (T := c)).repr.injective
  refine lp.ext (funext fun n => ?_)
  have h1 := fourierCoeff_perLp (deriv F) (hF.continuous_deriv le_rfl) (periodic_deriv hper) n
  have h2 := fourierCoeff_perLp F hF.continuous hper n
  rw [repr_Jq, fourierBasis_repr, fourierBasis_repr, h1, h2]
  have hab := lt_add_of_pos_right (0 : ℝ) hc.out
  rcases eq_or_ne n 0 with rfl | hn
  · rw [jqSymbol_zero, zero_mul, fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, zero_add, hmean, smul_zero]
  · have hd : ∀ x ∈ uIcc 0 (0 + c), HasDerivAt F (deriv F x) x := fun x _ =>
      (hF.differentiable one_ne_zero x).hasDerivAt
    have hi : IntervalIntegrable (deriv F) volume 0 (0 + c) :=
      (hF.continuous_deriv le_rfl).intervalIntegrable _ _
    rw [fourierCoeffOn_of_hasDerivAt hab hn hd hi]
    have hFc : F (0 + c) - F 0 = 0 := by
      have := hper 0
      simp only [zero_add] at this ⊢
      rw [this, sub_self]
    rw [hFc, mul_zero, zero_sub, jqSymbol_of_ne hn]
    have : (2 * π * I * n : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, hn, Complex.I_ne_zero]
    simp only [zero_add, sub_zero, Complex.ofReal_zero]
    field_simp

end Operator

end UnforcedLeray.Cyl
