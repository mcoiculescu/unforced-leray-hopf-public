import UnforcedLeray.Short.PartIIa.Sub.N02_4_4

/-!
# Part II-a, task `PartII-a:N02/4/4` (`NzQParseval`): `q`-orthogonality of modes on one period

Target: `NzQParseval` (`Short/PartII-a/Sub/N02_4_4.lean`). Source of record:
`the November 2 reference manuscript`, lines 1713-1727 (nonzero `q`-frequencies)
and 1744-1745 (finite Fourier sums).

Statement: `∫_0^c ‖Σ_{n∈M} e^{2π i n q / c} v_n‖² dq = c Σ_{n∈M} ‖v_n‖²`.

Proof: `‖x‖² = ⟪x, x⟫` (as a complex number) expands into the double sum of `conj(e_n) e_m ⟪v_n, v_m⟫`.
The `q`-integral of `conj(e_n) e_m` is `c δ_{nm}` by the closed form of the exponential integral,
since `exp(2π i k) = 1` for integers `k`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The `q`-mode `e^{2π i n q / c}`. -/
def nzqpE (c : ℝ) (n : ℤ) (q : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))

lemma nzqp_conj_mul (c : ℝ) (n m : ℤ) (q : ℝ) :
    starRingEnd ℂ (nzqpE c n q) * nzqpE c m q =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) - (n : ℂ)) * (q : ℂ) / (c : ℂ)) := by
  unfold nzqpE
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  ring

lemma nzqp_integral_conj_mul (c : ℝ) (hc : 0 < c) (n m : ℤ) :
    ∫ q in (0 : ℝ)..c, starRingEnd ℂ (nzqpE c n q) * nzqpE c m q =
      if n = m then (c : ℂ) else 0 := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  simp_rw [nzqp_conj_mul c n m]
  by_cases h : n = m
  · subst h
    simp [Complex.real_smul]
  · rw [if_neg h]
    have hk : (m : ℂ) - (n : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (fun h' => h (by exact_mod_cast h'.symm))
    have ha : 2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) - (n : ℂ)) / (c : ℂ) ≠ 0 := by
      refine div_ne_zero ?_ hcC
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) hk
    have hfun : ∀ q : ℝ,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) - (n : ℂ)) * (q : ℂ) / (c : ℂ)) =
          Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) - (n : ℂ)) / (c : ℂ)) * (q : ℂ)) := by
      intro q
      congr 1
      ring
    simp_rw [hfun]
    rw [integral_exp_mul_complex ha]
    have hend : 2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) - (n : ℂ)) / (c : ℂ) * (c : ℂ) =
        ((m - n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [div_mul_cancel₀ _ hcC]
      push_cast
      ring
    rw [hend, Complex.exp_int_mul_two_pi_mul_I]
    simp

lemma nzqp_inner_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    inner ℂ x x = (((‖x‖ ^ 2 : ℝ)) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

lemma nzqp_pt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : ℝ) (M : Finset ℤ)
    (v : ℤ → E) (q : ℝ) :
    (((‖∑ n ∈ M, nzqpE c n q • v n‖ ^ 2 : ℝ)) : ℂ) =
      ∑ n ∈ M, ∑ m ∈ M, starRingEnd ℂ (nzqpE c n q) * nzqpE c m q * inner ℂ (v n) (v m) := by
  rw [← nzqp_inner_self]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

theorem nzQParseval : NzQParseval := by
  unfold NzQParseval
  intro c hc M v
  show ∫ q in (0 : ℝ)..c, ‖∑ n ∈ M, nzqpE c n q • v n‖ ^ 2 = c * ∑ n ∈ M, ‖v n‖ ^ 2
  have hcont : ∀ (n m : ℤ) (w : ℂ),
      Continuous (fun q : ℝ => starRingEnd ℂ (nzqpE c n q) * nzqpE c m q * w) := by
    intro n m w
    have h1 : Continuous fun q : ℝ => nzqpE c n q := by
      unfold nzqpE
      fun_prop
    have h2 : Continuous fun q : ℝ => nzqpE c m q := by
      unfold nzqpE
      fun_prop
    exact ((Complex.continuous_conj.comp h1).mul h2).mul continuous_const
  have hint : ∀ (n m : ℤ) (w : ℂ),
      ∫ q in (0 : ℝ)..c, starRingEnd ℂ (nzqpE c n q) * nzqpE c m q * w =
        (if n = m then (c : ℂ) else 0) * w := by
    intro n m w
    rw [intervalIntegral.integral_mul_const, nzqp_integral_conj_mul c hc n m]
  have hsum : ∀ n ∈ M, ∫ q in (0 : ℝ)..c,
      ∑ m ∈ M, starRingEnd ℂ (nzqpE c n q) * nzqpE c m q * inner ℂ (v n) (v m) =
        (c : ℂ) * inner ℂ (v n) (v n) := by
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.sum_eq_single n]
      · rw [hint n n (inner ℂ (v n) (v n))]
        simp
      · intro m _ hm
        rw [hint n m (inner ℂ (v n) (v m))]
        simp [Ne.symm hm]
      · intro h
        exact absurd hn h
    · intro m _
      exact (hcont n m (inner ℂ (v n) (v m))).intervalIntegrable _ _
  have hall : ∫ q in (0 : ℝ)..c, ∑ n ∈ M, ∑ m ∈ M,
      starRingEnd ℂ (nzqpE c n q) * nzqpE c m q * inner ℂ (v n) (v m) =
        ∑ n ∈ M, (c : ℂ) * inner ℂ (v n) (v n) := by
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl hsum
    · intro n _
      exact (continuous_finsetSum M (fun m _ => hcont n m (inner ℂ (v n) (v m)))).intervalIntegrable
        _ _
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [nzqp_pt c M v]
  rw [hall, ← Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => nzqp_inner_self (v n))

end UnforcedLeray.Short.PartIIa
