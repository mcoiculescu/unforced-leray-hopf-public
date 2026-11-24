import UnforcedLeray.Short.PartIIa.Sub.N02_4_10
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.QParseval

/-!
# Part II-a, task `PartII-a:N02/4/10/4` (`NtmBesselPt`): Bessel inequality in `q` at fixed `(s, η)`

Target: `ntmBesselPt : NtmBesselPt` (`Sub/N02_4_10.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

For `φ(q) = g(s, q, η)` and the Fourier coefficients `a_n = nzCoeff c n g (s, η)` (`n ∈ M`,
`M = {0 < |n| ≤ N}`), let `T(q) = Σ_{n∈M} e^{2π i n q/c} a_n`. Then
* `∫_0^c ‖T‖² = c Σ_{n∈M} ‖a_n‖²` (`nzQParseval`);
* `∫_0^c Re⟪T, φ⟫ = c Σ_{n∈M} ‖a_n‖²` (each term: `conj(e_n) φ` integrates to `c a_n`);
* `0 ≤ ∫_0^c ‖T - φ‖² = ∫‖T‖² - 2 ∫Re⟪T,φ⟫ + ∫‖φ‖²`, so `∫‖T‖² ≤ ∫‖φ‖²`.
The vector-valued inner product is that of `MeridC = ℂ²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The truncated mode sum `q ↦ Σ_{n∈M} e^{2π i n q / c} a_n`. -/
def bpT (c : ℝ) (M : Finset ℤ) (a : ℤ → MeridC) (q : ℝ) : MeridC :=
  ∑ n ∈ M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • a n

/-- `conj(e^{2π i n q/c}) = e^{-2π i n q/c}`. -/
theorem bp_conj_exp (c q : ℝ) (n : ℤ) :
    starRingEnd ℂ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  ring

/-- Continuity of `q ↦ e^{-2π i n q/c} φ(q)`. -/
theorem bp_cont_w (c : ℝ) (n : ℤ) (φ : ℝ → MeridC) (hφ : Continuous φ) :
    Continuous fun q : ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) • φ q := by
  have h1 : Continuous fun q : ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) := by
    fun_prop
  exact h1.smul hφ

/-- One mode: `∫_0^c Re⟪e^{2π i n q/c} a, φ(q)⟫ dq = c ‖a‖²` when `a` is the `n`-th coefficient
of `φ`. -/
theorem bp_inner_term (c : ℝ) (hc : 0 < c) (n : ℤ) (a : MeridC) (φ : ℝ → MeridC)
    (hφ : Continuous φ)
    (ha : a = ((1 / c : ℝ) : ℂ) • ∫ q in (0 : ℝ)..c,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) • φ q) :
    ∫ q in (0 : ℝ)..c,
        (⟪Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • a,
          φ q⟫_ℂ).re
      = c * ‖a‖ ^ 2 := by
  have hwc := bp_cont_w c n φ hφ
  have hpt : ∀ q : ℝ,
      ⟪Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • a, φ q⟫_ℂ =
        ⟪a, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
          φ q⟫_ℂ := by
    intro q
    rw [inner_smul_left, inner_smul_right, bp_conj_exp]
  simp_rw [hpt]
  have hi : IntervalIntegrable (fun q : ℝ =>
      ⟪a, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) • φ q⟫_ℂ)
      volume 0 c :=
    (continuous_const.inner hwc).intervalIntegrable 0 c
  have hre : ∫ q in (0 : ℝ)..c,
      (⟪a, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
        φ q⟫_ℂ).re =
      (∫ q in (0 : ℝ)..c,
        ⟪a, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
          φ q⟫_ℂ).re := by
    have h := Complex.reCLM.intervalIntegral_comp_comm hi
    simpa using h
  have hL : ∫ q in (0 : ℝ)..c,
      ⟪a, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
        φ q⟫_ℂ =
      ⟪a, ∫ q in (0 : ℝ)..c,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
          φ q⟫_ℂ :=
    (innerSL ℂ a).intervalIntegral_comp_comm (hwc.intervalIntegrable 0 c)
  have hint : ∫ q in (0 : ℝ)..c,
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) • φ q =
      ((c : ℝ) : ℂ) • a := by
    rw [ha, smul_smul, ← Complex.ofReal_mul, mul_one_div_cancel hc.ne', Complex.ofReal_one,
      one_smul]
  rw [hre, hL, hint, inner_smul_right, inner_self_eq_norm_sq_to_K]
  first
    | simp [sq]
    | simp [sq, Complex.re_ofReal_mul]
    | norm_num [sq, Complex.mul_re]

/-- **Bessel inequality for the mode sum.** For continuous `φ` with Fourier coefficients `a n`,
the truncated mode sum has no larger `L²(0, c)` norm than `φ`. -/
theorem bp_bessel (c : ℝ) (hc : 0 < c) (M : Finset ℤ) (φ : ℝ → MeridC) (hφ : Continuous φ)
    (a : ℤ → MeridC)
    (ha : ∀ n, a n = ((1 / c : ℝ) : ℂ) • ∫ q in (0 : ℝ)..c,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) • φ q) :
    ∫ q in (0 : ℝ)..c, ‖bpT c M a q‖ ^ 2 ≤ ∫ q in (0 : ℝ)..c, ‖φ q‖ ^ 2 := by
  have hTc : Continuous (bpT c M a) := by
    unfold bpT
    fun_prop
  have hPar : ∫ q in (0 : ℝ)..c, ‖bpT c M a q‖ ^ 2 = c * ∑ n ∈ M, ‖a n‖ ^ 2 :=
    nzQParseval c hc M a
  have hsum : ∀ q : ℝ, (⟪bpT c M a q, φ q⟫_ℂ).re =
      ∑ n ∈ M, (⟪Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • a n,
        φ q⟫_ℂ).re := by
    intro q
    unfold bpT
    rw [sum_inner, Complex.re_sum]
  have hBint : ∫ q in (0 : ℝ)..c, (⟪bpT c M a q, φ q⟫_ℂ).re = c * ∑ n ∈ M, ‖a n‖ ^ 2 := by
    simp_rw [hsum]
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      exact bp_inner_term c hc n (a n) φ hφ (ha n)
    · intro n _
      have hf : Continuous fun q : ℝ =>
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • a n := by
        fun_prop
      exact (Complex.continuous_re.comp (hf.inner hφ)).intervalIntegrable 0 c
  have hpt : ∀ q : ℝ, ‖bpT c M a q - φ q‖ ^ 2 =
      ‖bpT c M a q‖ ^ 2 - 2 * (⟪bpT c M a q, φ q⟫_ℂ).re + ‖φ q‖ ^ 2 :=
    fun q => by
      first
        | exact norm_sub_sq (𝕜 := ℂ) _ _
        | simpa using norm_sub_sq (𝕜 := ℂ) (bpT c M a q) (φ q)
  have h0 : 0 ≤ ∫ q in (0 : ℝ)..c, ‖bpT c M a q - φ q‖ ^ 2 :=
    intervalIntegral.integral_nonneg hc.le fun q _ => by positivity
  simp_rw [hpt] at h0
  have hA : IntervalIntegrable (fun q : ℝ => ‖bpT c M a q‖ ^ 2) volume 0 c :=
    ((hTc.norm).pow 2).intervalIntegrable 0 c
  have hB : IntervalIntegrable (fun q : ℝ => (⟪bpT c M a q, φ q⟫_ℂ).re) volume 0 c :=
    (Complex.continuous_re.comp (hTc.inner hφ)).intervalIntegrable 0 c
  have hC : IntervalIntegrable (fun q : ℝ => ‖φ q‖ ^ 2) volume 0 c :=
    ((hφ.norm).pow 2).intervalIntegrable 0 c
  rw [intervalIntegral.integral_add (hA.sub (hB.const_mul 2)) hC,
    intervalIntegral.integral_sub hA (hB.const_mul 2),
    intervalIntegral.integral_const_mul, hBint, hPar] at h0
  rw [hPar]
  linarith

/-- **`NtmBesselPt` (target).** For a smooth test `g`, the `q`-truncation has no larger `q`-moment
than `g` at each `(s, η)`. -/
theorem ntmBesselPt : NtmBesselPt := by
  intro c hc g hg N s η
  have hφ : Continuous fun q : ℝ => g (s, q, η) :=
    hg.smooth.continuous.comp (by fun_prop)
  exact bp_bessel c hc ((Finset.Icc (-(N : ℤ)) N).erase 0) (fun q => g (s, q, η)) hφ
    (fun n => nzCoeff c n g (s, η)) (fun n => rfl)

end UnforcedLeray.Short.PartIIa
