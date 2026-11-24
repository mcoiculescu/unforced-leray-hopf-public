import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1.Riemann
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Riemann sums of the slice derivatives

For `r` with `|r - s| < ε`, the left Riemann sums `riemannSlice F s r n z` of `t ↦ ∂ₜF t z` over
`[s, r]` are finite sums of a.e. measurable slices, converge pointwise to `F r z - F s z`, and
satisfy the Cauchy-Schwarz bound `(riemannSlice)² ≤ ((r-s)²/n) ∑ₖ (∂ₜF t_k)²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.Short.PartI.L2SqDeriv

theorem slice_sample_dist {s r ε : ℝ} (hr : |r - s| < ε) {n k : ℕ} (hk : k < n) :
    |s + (k : ℝ) * ((r - s) / n) - s| < ε := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk.le
  have h1 : (k : ℝ) / n ≤ 1 := (div_le_one hn).2 hk'
  have h0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
  have e : s + (k : ℝ) * ((r - s) / n) - s = ((k : ℝ) / n) * (r - s) := by ring
  rw [e, abs_mul, abs_of_nonneg h0]
  calc (k : ℝ) / n * |r - s| ≤ 1 * |r - s| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |r - s| := one_mul _
    _ < ε := hr

/-- The left Riemann sum over `[s, r]` of the slice derivatives `t ↦ ∂ₜF t z`. -/
def riemannSlice (F : ℝ → UnforcedLeray.Cyl.Plane → ℝ) (s r : ℝ) (n : ℕ)
    (z : UnforcedLeray.Cyl.Plane) : ℝ :=
  ∑ k ∈ Finset.range n, (r - s) / (n : ℝ) * deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))

theorem riemannSlice_aesm {μ : Measure UnforcedLeray.Cyl.Plane} (F : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (s ε r : ℝ) (hr : |r - s| < ε)
    (hD : ∀ t, |t - s| < ε → AEStronglyMeasurable (fun z => deriv (fun t' => F t' z) t) μ)
    (n : ℕ) : AEStronglyMeasurable (riemannSlice F s r n) μ := by
  unfold riemannSlice
  refine Finset.aestronglyMeasurable_fun_sum (Finset.range n) fun k hk => ?_
  exact (hD _ (slice_sample_dist hr (Finset.mem_range.1 hk))).const_mul _

theorem riemannSlice_tendsto (F : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (hC : ∀ z, ContDiff ℝ 1 (fun t => F t z)) (s r : ℝ) (z : UnforcedLeray.Cyl.Plane) :
    Tendsto (fun n => riemannSlice F s r n z) atTop (𝓝 (F r z - F s z)) := by
  have hcont : Continuous (fun t => deriv (fun t' => F t' z) t) :=
    (hC z).continuous_deriv (by norm_num)
  have h1 := tendsto_riemannSum (fun t => deriv (fun t' => F t' z) t) hcont s r
  have hFTC : ∫ t in s..r, deriv (fun t' => F t' z) t = F r z - F s z :=
    intervalIntegral.integral_deriv_eq_sub' (fun t => F t z) rfl
      (fun t _ => ((hC z).differentiable (by norm_num)) t) hcont.continuousOn
  rw [← hFTC]
  exact h1

theorem riemannSlice_sq_le (F : ℝ → UnforcedLeray.Cyl.Plane → ℝ) (s r : ℝ) (n : ℕ)
    (z : UnforcedLeray.Cyl.Plane) :
    (riemannSlice F s r n z) ^ 2 ≤ ((r - s) ^ 2 / (n : ℝ)) *
      ∑ k ∈ Finset.range n, (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [riemannSlice]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.range n)
      (f := fun k : ℕ => (r - s) / (n : ℝ) * deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n)))
    rw [Finset.card_range] at hCS
    have e : ∑ k ∈ Finset.range n, ((r - s) / (n : ℝ) * deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2
        = ((r - s) / (n : ℝ)) ^ 2 * ∑ k ∈ Finset.range n, (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hc : (n : ℝ) * ((r - s) / (n : ℝ)) ^ 2 = (r - s) ^ 2 / (n : ℝ) := by
      field_simp
    unfold riemannSlice
    refine hCS.trans (le_of_eq ?_)
    rw [e]
    calc (n : ℝ) * (((r - s) / (n : ℝ)) ^ 2 * ∑ k ∈ Finset.range n, (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2)
        = ((n : ℝ) * ((r - s) / (n : ℝ)) ^ 2) * ∑ k ∈ Finset.range n, (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2 := by ring
      _ = _ := by rw [hc]

theorem riemannSlice_sq_integral_le {μ : Measure UnforcedLeray.Cyl.Plane}
    (F : ℝ → UnforcedLeray.Cyl.Plane → ℝ) (s ε K r : ℝ) (hr : |r - s| < ε) (hK : 0 ≤ K)
    (hD : ∀ t, |t - s| < ε → MemLp (fun z => deriv (fun t' => F t' z) t) 2 μ ∧
      ∫ z, (deriv (fun t' => F t' z) t) ^ 2 ∂μ ≤ K) (n : ℕ) :
    ∫ z, ((r - s) ^ 2 / (n : ℝ)) *
      ∑ k ∈ Finset.range n, (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2 ∂μ
      ≤ (r - s) ^ 2 * K := by
  have hint : ∀ k ∈ Finset.range n,
      Integrable (fun z => (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2) μ :=
    fun k hk => (hD _ (slice_sample_dist hr (Finset.mem_range.1 hk))).1.integrable_sq
  rw [integral_const_mul, integral_finsetSum _ hint]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero, zero_mul]
    exact mul_nonneg (sq_nonneg _) hK
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsum : ∑ k ∈ Finset.range n,
        ∫ z, (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2 ∂μ ≤ ∑ k ∈ Finset.range n, K :=
      Finset.sum_le_sum fun k hk => (hD _ (slice_sample_dist hr (Finset.mem_range.1 hk))).2
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    calc ((r - s) ^ 2 / (n : ℝ)) * ∑ k ∈ Finset.range n,
          ∫ z, (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2 ∂μ
        ≤ ((r - s) ^ 2 / (n : ℝ)) * ((n : ℝ) * K) :=
          mul_le_mul_of_nonneg_left hsum (div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))
      _ = (r - s) ^ 2 * K := by field_simp

end UnforcedLeray.Short.PartI.L2SqDeriv
