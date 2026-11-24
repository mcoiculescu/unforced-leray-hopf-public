import UnforcedLeray.Short.PartIIa.Sub.N02_4_10
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncTest
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ModeSplit.IntervalParamSmooth

/-!
# Part II-a, task `PartII-a:N02/4/10/2` (`NtmTruncTest`): truncations of smooth tests

Target: `ntmTruncTest : NtmTruncTest` (`Sub/N02_4_10.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

This is the sibling `nzTruncTest` (`NonzeroMode/TruncTest.lean`) with the mean-zero hypothesis
removed. The truncation `nzTrunc c N g` is a finite sum of `e^{2πi n q/c} a_n(s,η)` with
`a_n = nzCoeff c n g`; each `a_n` is smooth (`IntervalParamSmooth`), each term is supported in the
band of `g`, and each term is `c`-periodic in `q`. The helper lemmas `nztt_coeff_smooth`,
`nztt_coeff_zero`, `nztt_exp_cd` and `nztt_proj_cd` are imported from `NonzeroMode/TruncTest.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **`NtmTruncTest` (target).** -/
theorem ntmTruncTest : NtmTruncTest := by
  intro c hc g hg N
  obtain ⟨s0, s1, L, hs0, hb⟩ := hg.band
  have hsm : ∀ n : ℤ, ContDiff ℝ ∞ (nzCoeff c n g) :=
    fun n => nztt_coeff_smooth intervalParamSmooth_proof c n g hg.smooth
  -- smoothness of the truncation
  have hsmooth : ContDiff ℝ ∞ (nzTrunc c N g) := by
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
  have hper : QPeriodic c (nzTrunc c N g) := by
    intro p
    unfold nzTrunc
    dsimp only
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hexp n p.2.1]
  -- band of the truncation
  have hband : ∀ p : Profile, nzTrunc c N g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
    intro p hp
    by_contra h
    apply hp
    unfold nzTrunc
    apply Finset.sum_eq_zero
    intro n _
    rw [nztt_coeff_zero c n g s0 s1 L hb (p.1, p.2.2) h, smul_zero]
  exact ⟨hsmooth, hper, ⟨s0, s1, L, hs0, hband⟩⟩

end UnforcedLeray.Short.PartIIa
