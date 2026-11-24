import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Minkowski inequality for two finite families of reals (Cauchy-Schwarz form). -/
theorem nzfpMink (M : Finset ℤ) (p q : ℤ → ℝ) :
    ∑ n ∈ M, (p n + q n) ^ 2 ≤ (√(∑ n ∈ M, p n ^ 2) + √(∑ n ∈ M, q n ^ 2)) ^ 2 := by
  have hA : √(∑ n ∈ M, p n ^ 2) ^ 2 = ∑ n ∈ M, p n ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun n _ => sq_nonneg _)
  have hB : √(∑ n ∈ M, q n ^ 2) ^ 2 = ∑ n ∈ M, q n ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun n _ => sq_nonneg _)
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt M p q
  have e : ∑ n ∈ M, (p n + q n) ^ 2
      = ∑ n ∈ M, p n ^ 2 + 2 * ∑ n ∈ M, p n * q n + ∑ n ∈ M, q n ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [e, add_sq, hA, hB]
  nlinarith [hCS]

/-- Abstract real-analysis bound: `Σ x_n² ≤ 2K² (√Z₀ + √Z₁)²`. -/
theorem nzfpKeyAbs (M : Finset ℤ) (K : ℝ) (x a0 b0 a1 b1 : ℤ → ℝ)
    (hx : ∀ n ∈ M, 0 ≤ x n)
    (hb : ∀ n ∈ M, x n ≤ K * ((a0 n + b0 n) + (a1 n + b1 n))) :
    ∑ n ∈ M, x n ^ 2 ≤
      2 * K ^ 2 * (√(∑ n ∈ M, (a0 n ^ 2 + b0 n ^ 2)) + √(∑ n ∈ M, (a1 n ^ 2 + b1 n ^ 2))) ^ 2 := by
  have s1 : ∑ n ∈ M, x n ^ 2 ≤ ∑ n ∈ M, (K * ((a0 n + b0 n) + (a1 n + b1 n))) ^ 2 :=
    Finset.sum_le_sum fun n hn => pow_le_pow_left₀ (hx n hn) (hb n hn) 2
  have e1 : ∑ n ∈ M, (K * ((a0 n + b0 n) + (a1 n + b1 n))) ^ 2
      = K ^ 2 * ∑ n ∈ M, ((a0 n + b0 n) + (a1 n + b1 n)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have s2 : ∑ n ∈ M, ((a0 n + b0 n) + (a1 n + b1 n)) ^ 2 ≤
      (√(∑ n ∈ M, (a0 n + b0 n) ^ 2) + √(∑ n ∈ M, (a1 n + b1 n) ^ 2)) ^ 2 :=
    nzfpMink M (fun n => a0 n + b0 n) (fun n => a1 n + b1 n)
  have t0 : ∑ n ∈ M, (a0 n + b0 n) ^ 2 ≤ 2 * ∑ n ∈ M, (a0 n ^ 2 + b0 n ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => by nlinarith [sq_nonneg (a0 n - b0 n)]
  have t1 : ∑ n ∈ M, (a1 n + b1 n) ^ 2 ≤ 2 * ∑ n ∈ M, (a1 n ^ 2 + b1 n ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => by nlinarith [sq_nonneg (a1 n - b1 n)]
  have r0 : √(∑ n ∈ M, (a0 n + b0 n) ^ 2) ≤ √2 * √(∑ n ∈ M, (a0 n ^ 2 + b0 n ^ 2)) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt t0
  have r1 : √(∑ n ∈ M, (a1 n + b1 n) ^ 2) ≤ √2 * √(∑ n ∈ M, (a1 n ^ 2 + b1 n ^ 2)) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt t1
  have hT : √(∑ n ∈ M, (a0 n + b0 n) ^ 2) + √(∑ n ∈ M, (a1 n + b1 n) ^ 2)
      ≤ √2 * (√(∑ n ∈ M, (a0 n ^ 2 + b0 n ^ 2)) + √(∑ n ∈ M, (a1 n ^ 2 + b1 n ^ 2))) := by
    rw [mul_add]
    linarith [r0, r1]
  have hnn : 0 ≤ √(∑ n ∈ M, (a0 n + b0 n) ^ 2) + √(∑ n ∈ M, (a1 n + b1 n) ^ 2) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ hnn hT 2
  have h2 : (√2 * (√(∑ n ∈ M, (a0 n ^ 2 + b0 n ^ 2)) + √(∑ n ∈ M, (a1 n ^ 2 + b1 n ^ 2)))) ^ 2
      = 2 * (√(∑ n ∈ M, (a0 n ^ 2 + b0 n ^ 2)) + √(∑ n ∈ M, (a1 n ^ 2 + b1 n ^ 2))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  calc ∑ n ∈ M, x n ^ 2 ≤ K ^ 2 * ∑ n ∈ M, ((a0 n + b0 n) + (a1 n + b1 n)) ^ 2 :=
        s1.trans_eq e1
    _ ≤ K ^ 2 * (√(∑ n ∈ M, (a0 n + b0 n) ^ 2) + √(∑ n ∈ M, (a1 n + b1 n) ^ 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left s2 (sq_nonneg K)
    _ ≤ K ^ 2 * (2 * (√(∑ n ∈ M, (a0 n ^ 2 + b0 n ^ 2)) + √(∑ n ∈ M, (a1 n ^ 2 + b1 n ^ 2))) ^ 2) :=
        mul_le_mul_of_nonneg_left (hsq.trans h2.le) (sq_nonneg K)
    _ = 2 * K ^ 2 * (√(∑ n ∈ M, (a0 n ^ 2 + b0 n ^ 2)) + √(∑ n ∈ M, (a1 n ^ 2 + b1 n ^ 2))) ^ 2 := by
        ring

/-- Square-root step: from `S ≤ 2K²(√Z₀ + √Z₁)²` deduce the rpow bound with constant `√2 K`. -/
theorem nzfpSqrtStep (c S Z0 Z1 K : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hS : S ≤ 2 * K ^ 2 * (√Z0 + √Z1) ^ 2) :
    (c * S) ^ (1 / 2 : ℝ) ≤ √2 * K * ((c * Z0) ^ (1 / 2 : ℝ) + (c * Z1) ^ (1 / 2 : ℝ)) := by
  simp only [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_mul hc S, Real.sqrt_mul hc Z0, Real.sqrt_mul hc Z1]
  have hnn : 0 ≤ √2 * K * (√Z0 + √Z1) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hS2 : S ≤ (√2 * K * (√Z0 + √Z1)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    linarith [hS]
  have hsS : √S ≤ √2 * K * (√Z0 + √Z1) := Real.sqrt_le_iff.mpr ⟨hnn, hS2⟩
  calc √c * √S ≤ √c * (√2 * K * (√Z0 + √Z1)) :=
        mul_le_mul_of_nonneg_left hsS (Real.sqrt_nonneg c)
    _ = √2 * K * (√c * √Z0 + √c * √Z1) := by ring

/-- **Abstract family bound** (see the Sub file). -/
theorem nzFpFamilyBound : UnforcedLeray.Short.PartIIa.NzFpFamilyBound := by
  unfold NzFpFamilyBound
  intro c hc M a g K hK hm hsq hsqa
  unfold nzMomSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α hα
  have hkey : ∀ j ∈ Finset.range 2,
      ∑ n ∈ M, (nzMom2 j α (g n)) ^ 2 ≤
        2 * K ^ 2 * (√(∑ n ∈ M, (nzMom2 0 α (fun x => a n x 0) ^ 2 + nzMom2 0 α (fun x => a n x 1) ^ 2))
          + √(∑ n ∈ M, (nzMom2 1 α (fun x => a n x 0) ^ 2 + nzMom2 1 α (fun x => a n x 1) ^ 2))) ^ 2 := by
    intro j hj
    apply nzfpKeyAbs M K (fun n => nzMom2 j α (g n))
      (fun n => nzMom2 0 α (fun x => a n x 0)) (fun n => nzMom2 0 α (fun x => a n x 1))
      (fun n => nzMom2 1 α (fun x => a n x 0)) (fun n => nzMom2 1 α (fun x => a n x 1))
    · intro n _
      exact nzMom2_nonneg j α (g n)
    · intro n hn
      have h := hm n hn α hα j hj
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
      exact h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hsq α hα 0 (by simp), hsq α hα 1 (by simp), hsqa α hα 0 (by simp), hsqa α hα 1 (by simp)]
  have s0 := nzfpSqrtStep c _ _ _ K hc.le hK (hkey 0 (by simp))
  have s1 := nzfpSqrtStep c _ _ _ K hc.le hK (hkey 1 (by simp))
  refine (add_le_add s0 s1).trans (le_of_eq ?_)
  ring

end UnforcedLeray.Short.PartIIa
