import UnforcedLeray.Short.PartIIa.Sub.N02_4_11
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Int.Star

/-!
# Part II-a, `PartII-a:N02/4/11/1`: slice convergence of the Fourier truncations (`NzSliceConv`)

Target: `nzSliceConv : NzSliceConv` (`Sub/N02_4_11.lean`). Source of record:
`the November 2 reference manuscript`.

For a fixed slice `g(q) = f(s, q, η)` (continuous, `c`-periodic in `q` only through the
hypotheses used here, with zero `q`-integral over `(0, c]`), the truncation error is
`h_N = Σ_{0<|n|≤N} e_n a_n - g`, where `a_n` is the `n`-th Fourier coefficient of `g` on `(0, c]`.
The coefficients of `h_N` are `0` for `|n| ≤ N` and `a_n` for `|n| > N`. Parseval on `(0, c]`
(`hasSum_sq_fourierCoeffOn`, applied to the two real components of the `ℂ²`-valued slice) gives
`∫_0^c ‖h_N‖² = c Σ_{n} ‖coeff_n h_N‖²`, which is bounded by `∫_0^c ‖g‖²` and tends to `0`
by dominated convergence over `ℤ` (`tendsto_tsum_of_dominated_convergence`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace SliceConvAux

/-- The Fourier coefficient on `(0, c]` in the normalisation of `nzCoeff`. -/
theorem coeffOn_eq_exp {c : ℝ} (hc : 0 < c) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (F : ℝ → E) (n : ℤ) :
    fourierCoeffOn hc F n =
      ((1 / c : ℝ) : ℂ) • ∫ q in (0:ℝ)..c,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) • F q := by
  rw [fourierCoeffOn_eq_integral F n hc]
  have hI : (∫ x in (0:ℝ)..c, fourier (-n) (x : AddCircle (c - 0)) • F x)
      = ∫ q in (0:ℝ)..c, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)))
          • F q := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    congr 1
    rw [fourier_coe_apply]
    simp only [sub_zero]
    congr 1
    push_cast
    ring
  rw [hI, sub_zero, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- Orthogonality of the `q`-exponentials on `(0, c]`, with the coefficient normalisation. -/
theorem coeffOn_exp_orth {c : ℝ} (hc : 0 < c) (n i : ℤ) (v : MeridC) :
    ((1 / c : ℝ) : ℂ) • (∫ q in (0:ℝ)..c,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) •
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • v))
      = if n = i then v else 0 := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  split_ifs with h
  · subst h
    have hfun : ∀ q : ℝ,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) •
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • v) = v := by
      intro q
      rw [smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
    simp only [hfun, intervalIntegral.integral_const, sub_zero]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c v, smul_smul]
    have h1 : ((1 / c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
      have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      push_cast
      field_simp
    exact (congrArg (fun x : ℂ => x • v) h1).trans (one_smul ℂ v)
  · have hni : ((n : ℂ) - (i : ℂ)) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
    have hκ : (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) - (i : ℂ)) / (c : ℂ)) ≠ 0 := by
      apply div_ne_zero _ hc'
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero) hni
    have hfun : ∀ q : ℝ,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) •
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • v)
        = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) - (i : ℂ)) / (c : ℂ)) * (q : ℂ))
          • v := by
      intro q
      rw [smul_smul, ← Complex.exp_add]
      congr 2
      ring
    simp only [hfun]
    rw [intervalIntegral.integral_smul_const, integral_exp_mul_complex hκ]
    have hk : (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) - (i : ℂ)) / (c : ℂ)) * ((c : ℝ) : ℂ)
        = ((n - i : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      field_simp
    rw [hk, Complex.exp_int_mul_two_pi_mul_I, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      sub_self, zero_div, zero_smul, smul_zero]

/-- The Fourier coefficients of a finite sum of exponentials times vectors. -/
theorem coeffOn_sum_exp {c : ℝ} (hc : 0 < c) (F : Finset ℤ) (v : ℤ → MeridC) (i : ℤ) :
    fourierCoeffOn hc (fun q : ℝ => ∑ n ∈ F,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • v n) i
      = if i ∈ F then v i else 0 := by
  rw [coeffOn_eq_exp hc]
  have hsum : ∀ q : ℝ,
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) •
        (∑ n ∈ F, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • v n)
      = ∑ n ∈ F, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) •
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • v n) := by
    intro q
    rw [Finset.smul_sum]
  simp only [hsum]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.smul_sum]
    rw [Finset.sum_congr rfl (fun n _ => coeffOn_exp_orth hc n i (v n))]
    rw [Finset.sum_ite_eq']
  · intro n _
    exact (by fun_prop : Continuous fun q : ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) •
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) • v n)).intervalIntegrable _ _

/-- Linearity of the coefficient for continuous functions. -/
theorem coeffOn_sub {c : ℝ} (hc : 0 < c) {A B : ℝ → MeridC} (hA : Continuous A)
    (hB : Continuous B) (i : ℤ) :
    fourierCoeffOn hc (fun q => A q - B q) i = fourierCoeffOn hc A i - fourierCoeffOn hc B i := by
  simp only [coeffOn_eq_exp hc]
  have h1 : IntervalIntegrable (fun q : ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) • A q)
      MeasureTheory.volume 0 c :=
    (by fun_prop : Continuous fun q : ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) • A q).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun q : ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) • B q)
      MeasureTheory.volume 0 c :=
    (by fun_prop : Continuous fun q : ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) • B q).intervalIntegrable _ _
  rw [← smul_sub, ← intervalIntegral.integral_sub h1 h2]
  congr 1
  apply intervalIntegral.integral_congr
  intro q _
  simp only [smul_sub]

/-- Continuity of a slice of `ℂ²`-valued functions on `(0, c]`: an `L²` bound. -/
theorem memLp_Ioc_of_continuous {c : ℝ} {g : ℝ → ℂ} (hg : Continuous g) :
    MemLp g 2 (volume.restrict (Ioc 0 c)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := c)).exists_bound_of_continuousOn
    hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => hC x (Ioc_subset_Icc_self hx)))

/-- Parseval for the `ℂ²`-valued continuous function `h` on `(0, c]`. -/
theorem parseval_meridC {c : ℝ} (hc : 0 < c) {h : ℝ → MeridC} (hh : Continuous h) :
    HasSum (fun i : ℤ => ‖fourierCoeffOn hc h i‖ ^ 2)
      (c⁻¹ * ∫ q in (0:ℝ)..c, ‖h q‖ ^ 2) := by
  have hsc : ∀ L : MeridC →L[ℂ] ℂ, ∀ i : ℤ,
      fourierCoeffOn hc (fun q => L (h q)) i = L (fourierCoeffOn hc h i) := by
    intro L i
    rw [coeffOn_eq_exp hc, coeffOn_eq_exp hc, map_smul]
    congr 1
    have hint : IntervalIntegrable (fun q : ℝ =>
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) • h q)
        MeasureTheory.volume 0 c :=
      (by fun_prop : Continuous fun q : ℝ =>
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * (q : ℂ) / (c : ℂ))) • h q).intervalIntegrable _ _
    rw [← L.intervalIntegral_comp_comm hint]
    apply intervalIntegral.integral_congr
    intro q _
    simp only [map_smul]
  have hP : ∀ L : MeridC →L[ℂ] ℂ,
      HasSum (fun i : ℤ => ‖fourierCoeffOn hc (fun q => L (h q)) i‖ ^ 2)
        (c⁻¹ * ∫ q in (0:ℝ)..c, ‖L (h q)‖ ^ 2) := by
    intro L
    have hcont : Continuous (fun q => L (h q)) := L.continuous.comp hh
    have := hasSum_sq_fourierCoeffOn hc (memLp_Ioc_of_continuous (c := c) hcont)
    rwa [sub_zero, smul_eq_mul] at this
  let L0 : MeridC →L[ℂ] ℂ := EuclideanSpace.proj (0 : Fin 2)
  let L1 : MeridC →L[ℂ] ℂ := EuclideanSpace.proj (1 : Fin 2)
  have hA := (hP L0).add (hP L1)
  have hfun : (fun i : ℤ => ‖fourierCoeffOn hc h i‖ ^ 2)
      = fun i : ℤ => ‖fourierCoeffOn hc (fun q => L0 (h q)) i‖ ^ 2
          + ‖fourierCoeffOn hc (fun q => L1 (h q)) i‖ ^ 2 := by
    funext i
    rw [hsc L0 i, hsc L1 i, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [L0, L1]
  have hi0 : Continuous fun q => ‖L0 (h q)‖ ^ 2 := by fun_prop
  have hi1 : Continuous fun q => ‖L1 (h q)‖ ^ 2 := by fun_prop
  have hval : c⁻¹ * ∫ q in (0:ℝ)..c, ‖h q‖ ^ 2
      = c⁻¹ * (∫ q in (0:ℝ)..c, ‖L0 (h q)‖ ^ 2) + c⁻¹ * (∫ q in (0:ℝ)..c, ‖L1 (h q)‖ ^ 2) := by
    rw [← mul_add, ← intervalIntegral.integral_add (hi0.intervalIntegrable _ _) (hi1.intervalIntegrable _ _)]
    congr 1
    apply intervalIntegral.integral_congr
    intro q _
    simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, L0, L1]
    simp
  rw [hfun, hval]
  exact hA

end SliceConvAux

open SliceConvAux

/-- The truncation error `Σ_{0<|n|≤N} e_n a_n - g` on the slice `(0, c]`, with `a_n` the
coefficients of `g`. -/
theorem sliceAbstract {c : ℝ} (hc : 0 < c) {g : ℝ → MeridC} (hg : Continuous g)
    (hm : ∫ q in (0:ℝ)..c, g q = 0) :
    Tendsto (fun N : ℕ => ∫ q in (0:ℝ)..c,
        ‖(∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
              • fourierCoeffOn hc g n) - g q‖ ^ 2) atTop (𝓝 0) ∧
      ∀ N : ℕ, ∫ q in (0:ℝ)..c,
        ‖(∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
              • fourierCoeffOn hc g n) - g q‖ ^ 2
        ≤ 4 * ∫ q in (0:ℝ)..c, ‖g q‖ ^ 2 := by
  have ha0 : fourierCoeffOn hc g 0 = 0 := by
    rw [coeffOn_eq_exp hc]
    simp only [Int.cast_zero, mul_zero, zero_mul, zero_div, neg_zero, Complex.exp_zero, one_smul]
    rw [hm, smul_zero]
  have hTc : ∀ N : ℕ, Continuous (fun q : ℝ =>
      ∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
          • fourierCoeffOn hc g n) := by
    intro N
    fun_prop
  have hcoef : ∀ (N : ℕ) (i : ℤ),
      fourierCoeffOn hc (fun q => (∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
          • fourierCoeffOn hc g n) - g q) i
      = (if i ∈ (Finset.Icc (-(N : ℤ)) N).erase 0 then fourierCoeffOn hc g i else 0)
          - fourierCoeffOn hc g i := by
    intro N i
    rw [coeffOn_sub hc (hTc N) hg i, coeffOn_sum_exp hc _ (fun n => fourierCoeffOn hc g n) i]
  have hnorm : ∀ (N : ℕ) (i : ℤ),
      ‖fourierCoeffOn hc (fun q => (∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
          • fourierCoeffOn hc g n) - g q) i‖ ^ 2
      = if i ∈ (Finset.Icc (-(N : ℤ)) N).erase 0 then 0 else ‖fourierCoeffOn hc g i‖ ^ 2 := by
    intro N i
    rw [hcoef N i]
    by_cases h : i ∈ (Finset.Icc (-(N : ℤ)) N).erase 0 <;> simp [h]
  have hpar : ∀ N : ℕ, HasSum (fun i : ℤ => if i ∈ (Finset.Icc (-(N : ℤ)) N).erase 0 then 0
        else ‖fourierCoeffOn hc g i‖ ^ 2)
      (c⁻¹ * ∫ q in (0:ℝ)..c, ‖(∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
          • fourierCoeffOn hc g n) - g q‖ ^ 2) := by
    intro N
    have hcont : Continuous (fun q : ℝ => (∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
          • fourierCoeffOn hc g n) - g q) := (hTc N).sub hg
    have := parseval_meridC hc hcont
    convert this using 1
    funext i
    exact (hnorm N i).symm
  have hle : ∀ N : ℕ, c⁻¹ * (∫ q in (0:ℝ)..c, ‖(∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
          • fourierCoeffOn hc g n) - g q‖ ^ 2)
      ≤ c⁻¹ * ∫ q in (0:ℝ)..c, ‖g q‖ ^ 2 := by
    intro N
    have hg2 := parseval_meridC hc hg
    refine hasSum_le (fun i => ?_) (hpar N) hg2
    by_cases h : i ∈ (Finset.Icc (-(N : ℤ)) N).erase 0
    · simp only [h, ite_true]
      positivity
    · simp only [h, ite_false, le_refl]
  have hG0 : 0 ≤ ∫ q in (0:ℝ)..c, ‖g q‖ ^ 2 :=
    intervalIntegral.integral_nonneg hc.le (fun _ _ => sq_nonneg _)
  have hbound : ∀ N : ℕ, ∫ q in (0:ℝ)..c, ‖(∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
          • fourierCoeffOn hc g n) - g q‖ ^ 2 ≤ 4 * ∫ q in (0:ℝ)..c, ‖g q‖ ^ 2 := by
    intro N
    have := le_of_mul_le_mul_left (hle N) (inv_pos.2 hc)
    linarith
  have hE : ∀ N : ℕ, ∫ q in (0:ℝ)..c, ‖(∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
          • fourierCoeffOn hc g n) - g q‖ ^ 2
      = c * ∑' i : ℤ, (if i ∈ (Finset.Icc (-(N : ℤ)) N).erase 0 then 0
          else ‖fourierCoeffOn hc g i‖ ^ 2) := by
    intro N
    rw [(hpar N).tsum_eq, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have hsumg := (parseval_meridC hc hg).summable
  have hlim : Tendsto (fun N : ℕ => ∑' i : ℤ, (if i ∈ (Finset.Icc (-(N : ℤ)) N).erase 0 then 0
          else ‖fourierCoeffOn hc g i‖ ^ 2)) atTop (𝓝 0) := by
    have hsum2 : Summable (fun i : ℤ => ‖fourierCoeffOn hc g i‖ ^ 2) := by
      have := (parseval_meridC hc hg).summable
      exact this
    have key := tendsto_tsum_of_dominated_convergence
      (f := fun (N : ℕ) (i : ℤ) => if i ∈ (Finset.Icc (-(N : ℤ)) N).erase 0 then 0
          else ‖fourierCoeffOn hc g i‖ ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun i : ℤ => ‖fourierCoeffOn hc g i‖ ^ 2)
      hsum2
      (by
        intro i
        refine tendsto_atTop_of_eventually_const (i₀ := i.natAbs) (fun N hN => ?_)
        by_cases hi : i = 0
        · subst hi
          simp [ha0]
        · have hmem : i ∈ (Finset.Icc (-(N : ℤ)) N).erase 0 := by
            rw [Finset.mem_erase, Finset.mem_Icc]
            refine ⟨hi, ?_, ?_⟩ <;> omega
          simp [hmem])
      (Filter.Eventually.of_forall (fun N i => by
        by_cases h : i ∈ (Finset.Icc (-(N : ℤ)) N).erase 0 <;> simp [h]))
    simpa using key
  refine ⟨?_, hbound⟩
  have hc2 := hlim.const_mul c
  rw [mul_zero] at hc2
  exact Tendsto.congr (fun N => (hE N).symm) hc2

/-- **Target `PartII-a:N02/4/11/1`: slice convergence.** -/
theorem nzSliceConv : NzSliceConv := by
  intro c hc f hf hmean s η
  have hg : Continuous (fun q : ℝ => f (s, q, η)) :=
    hf.smooth.continuous.comp (by fun_prop)
  have hm : ∫ q in (0:ℝ)..c, f (s, q, η) = 0 := hmean s η
  have hT : ∀ (N : ℕ) (q : ℝ), nzTrunc c N f (s, q, η)
      = ∑ n ∈ (Finset.Icc (-(N : ℤ)) N).erase 0,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
            • fourierCoeffOn hc (fun q' : ℝ => f (s, q', η)) n := by
    intro N q
    simp only [nzTrunc]
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    rw [coeffOn_eq_exp hc]
    rfl
  obtain ⟨h1, h2⟩ := sliceAbstract hc hg hm
  refine ⟨?_, ?_⟩
  · simp only [hT]
    exact h1
  · intro N
    simp only [hT]
    exact h2 N

end UnforcedLeray.Short.PartIIa
