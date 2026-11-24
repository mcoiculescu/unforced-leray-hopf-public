import UnforcedLeray.Short.PartIIa.Sub.N02_4_2
import UnforcedLeray.Short.PartIIa.Sub.N02_5
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit.IntervalParamSmooth

/-!
# Part II-a, task `PartII-a:N02/4/2/T` (`NzTruncTest`): finite-mode zero-mean truncations

Target: `nzTruncTest : NzTruncTest` (`Sub/N02_4_2.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749 ("Initially use finite Fourier
sums, compact log-age support and Schwartz transverse profiles").

Route: for a smooth band test `f` with zero `q`-mean, the truncation `nzTrunc c N f` is a finite sum
`Σ_{n ∈ M} e^{2π i n q / c} a_n(s, η)` over `M = {0 < |n| ≤ N}` with `a_n = nzCoeff c n f`.

* smoothness of `a_n`: the parametric-integral leaf `IntervalParamSmooth` (`Sub/N02_5.lean`);
* band: `a_n` vanishes outside the `(s, η)`-band of `f`;
* periodicity and zero `q`-mean: the exponentials `e^{2π i n q / c}`, `n ≠ 0`.

`nzTruncTest_of` assumes the leaf `IntervalParamSmooth` (no other hypothesis). The unconditional
`nzTruncTest` is `nzTruncTest_of intervalParamSmooth_proof` once that leaf is proved (not in this file).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- The real-to-complex inclusion is smooth (`fun_prop` does not know it). -/
theorem nztt_ofReal_cd : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) :=
  Complex.ofRealCLM.contDiff

/-- The projection `(s, q, η) ↦ (s, η)` is smooth. -/
theorem nztt_proj_cd : ContDiff ℝ ∞ (fun p : Profile => (p.1, p.2.2)) := by
  fun_prop

/-- The `q`-character `q ↦ e^{2π i n q / c}` as a function of a profile, smooth. -/
theorem nztt_exp_cd (c : ℝ) (n : ℤ) :
    ContDiff ℝ ∞ (fun p : Profile =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (p.2.1 : ℂ) / (c : ℂ))) := by
  have hr : ContDiff ℝ ∞ (fun p : Profile => p.2.1) := by fun_prop
  have hR : ContDiff ℝ ∞ (fun p : Profile => (p.2.1 : ℂ)) := nztt_ofReal_cd.comp hr
  exact ((ContDiff.mul contDiff_const hR).div_const (c : ℂ)).cexp

/-- The Fourier coefficient `nzCoeff c n f` is smooth in `(s, η)`, by the leaf `IntervalParamSmooth`
applied to `H ((s, η), q) = e^{-2π i n q / c} f(s, q, η)`, which is smooth. -/
theorem nztt_coeff_smooth (hI : IntervalParamSmooth) (c : ℝ) (n : ℤ) (f : Profile → MeridC)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (nzCoeff c n f) := by
  have hofR : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => (z.2 : ℂ)) :=
    nztt_ofReal_cd.comp contDiff_snd
  have hE : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z.2 : ℂ) / (c : ℂ)))) :=
    ((ContDiff.mul contDiff_const hofR).div_const (c : ℂ)).neg.cexp
  have hF : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => f (z.1.1, z.2, z.1.2)) :=
    hf.comp (by fun_prop)
  have hH := (hI (ℝ × ℝ) MeridC 0 c
    (fun z : (ℝ × ℝ) × ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z.2 : ℂ) / (c : ℂ))) •
        f (z.1.1, z.2, z.1.2)) (hE.smul hF)).1
  unfold nzCoeff
  exact hH.const_smul ((1 / c : ℝ) : ℂ)

/-- A Fourier coefficient vanishes outside the band `s0 ≤ s ≤ s1`, `|η| ≤ L` of its profile. -/
theorem nztt_coeff_zero (c : ℝ) (n : ℤ) (f : Profile → MeridC) (s0 s1 L : ℝ)
    (hb : ∀ p : Profile, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) (x : ℝ × ℝ)
    (hx : ¬ (x.1 ∈ Icc s0 s1 ∧ |x.2| ≤ L)) : nzCoeff c n f x = 0 := by
  have h0 : ∀ q : ℝ, f (x.1, q, x.2) = 0 := by
    intro q
    by_contra h
    exact hx (hb (x.1, q, x.2) h)
  unfold nzCoeff
  simp only [h0, smul_zero, intervalIntegral.integral_zero]

/-- **`NzTruncTest` from the parametric-integral leaf.** The truncation of a smooth band test with
zero `q`-mean is an `IsMeridTest`, has zero `q`-mean, and has finitely many nonzero `q`-modes. -/
theorem nzTruncTest_of (hI : IntervalParamSmooth) : NzTruncTest := by
  intro c hc f hf _hmean N
  obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
  have hsm : ∀ n : ℤ, ContDiff ℝ ∞ (nzCoeff c n f) :=
    fun n => nztt_coeff_smooth hI c n f hf.smooth
  -- smoothness of the truncation
  have hsmooth : ContDiff ℝ ∞ (nzTrunc c N f) := by
    unfold nzTrunc
    apply ContDiff.sum
    intro n _
    exact (nztt_exp_cd c n).smul ((hsm n).comp nztt_proj_cd)
  -- `c`-periodicity of the exponentials with integer frequency
  have hexp : ∀ (n : ℤ) (q : ℝ),
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((q + c : ℝ) : ℂ) / (c : ℂ)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)) := by
    intro n q
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have key : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((q + c : ℝ) : ℂ) / (c : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)
          + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      field_simp
    rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hper : QPeriodic c (nzTrunc c N f) := by
    intro p
    unfold nzTrunc
    dsimp only
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hexp n p.2.1]
  -- band of the truncation
  have hband : ∀ p : Profile, nzTrunc c N f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
    intro p hp
    by_contra h
    apply hp
    unfold nzTrunc
    apply Finset.sum_eq_zero
    intro n _
    rw [nztt_coeff_zero c n f s0 s1 L hb (p.1, p.2.2) h, smul_zero]
  have hmer : IsMeridTest c (nzTrunc c N f) :=
    ⟨hsmooth, hper, ⟨s0, s1, L, hs0, hband⟩⟩
  -- zero `q`-mean of the truncation
  have hzero : QMeanZero c (nzTrunc c N f) := by
    intro s η
    unfold nzTrunc
    dsimp only
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_eq_zero fun n hn => ?_
      have hn0 : n ≠ 0 := Finset.ne_of_mem_erase hn
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hk : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (c : ℂ)) ≠ 0 :=
        div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hn')
          hc'
      have hexpint : (∫ q in (0 : ℝ)..c,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) = 0 := by
        have hfun : (fun q : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) /
              (c : ℂ))) = fun q : ℝ =>
            Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (c : ℂ)) * (q : ℂ)) := by
          funext q
          congr 1
          ring
        have hKc : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (c : ℂ)) * ((c : ℝ) : ℂ)
            = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
          field_simp
        rw [hfun, integral_exp_mul_complex hk, hKc, Complex.exp_int_mul_two_pi_mul_I]
        simp
      rw [intervalIntegral.integral_smul_const, hexpint, zero_smul]
    · intro n _
      apply Continuous.intervalIntegrable
      fun_prop
  -- finitely many nonzero modes
  have hfin : NzFinModes c (nzTrunc c N f) := by
    refine ⟨(Finset.Icc (-(N : ℤ)) N).erase 0, fun n => nzCoeff c n f,
      Finset.notMem_erase 0 _, ?_, ?_, ?_⟩
    · intro n _
      exact hsm n
    · intro n _
      refine ⟨s0, s1, L, hs0, fun x hx => ?_⟩
      by_contra h
      exact hx (nztt_coeff_zero c n f s0 s1 L hb x h)
    · intro p
      rfl
  exact ⟨hmer, hzero, hfin⟩

/-- **`NzTruncTest` (target).** The unconditional statement: `nzTruncTest_of` applied to the
compiled leaf proof `intervalParamSmooth_proof` (`Tasks/N02LerayComparison/ModeSplit/IntervalParamSmooth.lean`). -/
theorem nzTruncTest : NzTruncTest := nzTruncTest_of intervalParamSmooth_proof

end UnforcedLeray.Short.PartIIa
