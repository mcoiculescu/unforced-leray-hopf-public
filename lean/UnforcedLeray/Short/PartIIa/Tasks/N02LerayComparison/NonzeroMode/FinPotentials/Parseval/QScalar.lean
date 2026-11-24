import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4_7
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.QParseval

/-!
# Part II-a, task `PartII-a:N02/4/4/7/1`: scalar `q`-Parseval (`NzFpQScalar`)

The scalar case of `NzQParseval`. The proof is the same computation as `nzQParseval`
(in `QParseval.lean`), with the ambient space `E` kept general; it is instantiated at `E = ℂ`,
where `v n = z n`. The helper lemmas `nzqpE`, `nzqp_integral_conj_mul`, `nzqp_pt` and
`nzqp_inner_self` are reused from `QParseval.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartIIa

/-- The `q`-Parseval identity in a general complex inner product space. -/
theorem nzfpQ_gen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℝ) (hc : 0 < c) (M : Finset ℤ) (v : ℤ → E) :
    ∫ q in (0 : ℝ)..c, ‖∑ n ∈ M, nzqpE c n q • v n‖ ^ 2 = c * ∑ n ∈ M, ‖v n‖ ^ 2 := by
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

theorem nzFpQScalar : NzFpQScalar := by
  intro c hc M z
  exact nzfpQ_gen c hc M z

end UnforcedLeray.Short.PartIIa
