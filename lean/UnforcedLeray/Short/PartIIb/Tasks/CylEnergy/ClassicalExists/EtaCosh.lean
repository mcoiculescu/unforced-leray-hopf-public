import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages

/-!


Source of record: `the November 2 reference manuscript`, lines 2074-2093 and
2103-2105 (the weight `cosh η` in the cylinder equation). The statement is `EtaPowLeCosh`
(`Sub/T22_1/Plan.lean`): for every real `N` there is `C` with `(1 + η²)^N ≤ C · cosh η` for all `η`.

Proof. If `N ≤ 0`, the base is at least `1`, so `(1 + η²)^N ≤ 1 ≤ cosh η`; take `C = 1`.
If `N > 0`, pick `k : ℕ` with `N ≤ k`. Then `(1 + η²)^N ≤ (1 + η²)^k ≤ 2^(k-1) (1 + η^(2k))`
(`add_pow_le`). Since `|η|^(2k) / (2k)! ≤ exp |η| ≤ 2 cosh η` (`Real.pow_div_factorial_le_exp`,
`Real.exp_abs_le`), we get `1 + η^(2k) ≤ (1 + 2 (2k)!) cosh η`, using `1 ≤ cosh η`.
So `C = 2^(k-1) (1 + 2 (2k)!)` works.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-- **`T22/1/2`.** `(1 + η²)^N ≤ C cosh η` for every real `N`. -/
theorem etaPowLeCosh : UnforcedLeray.Short.IIb.CylPDE.EtaPowLeCosh := by
  intro N
  rcases le_or_gt N 0 with hN | hN
  · refine ⟨1, fun η => ?_⟩
    have hbase : (1 : ℝ) ≤ 1 + η ^ 2 := by linarith [sq_nonneg η]
    have h1 : (1 + η ^ 2) ^ N ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hbase hN
    have h2 : (1 : ℝ) ≤ Real.cosh η := Real.one_le_cosh η
    linarith
  · obtain ⟨k, hk⟩ := exists_nat_ge N
    have hFpos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    refine ⟨(2 : ℝ) ^ (k - 1) * (1 + 2 * (Nat.factorial (2 * k) : ℝ)), fun η => ?_⟩
    have hbase : (1 : ℝ) ≤ 1 + η ^ 2 := by linarith [sq_nonneg η]
    -- Step 1: lower the exponent from `N` to the natural number `k`.
    have s1 : (1 + η ^ 2) ^ N ≤ (1 + η ^ 2) ^ ((k : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase hk
    rw [Real.rpow_natCast] at s1
    -- Step 2: binomial bound `(1 + t)^k ≤ 2^(k-1) (1 + t^k)` for `t = η²`.
    have s2 : (1 + η ^ 2) ^ k ≤ (2 : ℝ) ^ (k - 1) * (1 + (η ^ 2) ^ k) := by
      have h := add_pow_le (zero_le_one : (0 : ℝ) ≤ 1) (sq_nonneg η) k
      rw [one_pow] at h
      exact h
    -- Step 3: `(η²)^k = |η|^(2k)`.
    have hpow : (η ^ 2) ^ k = |η| ^ (2 * k) := by
      rw [pow_mul, sq_abs]
    -- Step 4: `|η|^(2k) ≤ (2k)! exp |η| ≤ (2k)! · 2 cosh η`.
    have s3 : |η| ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) ≤ Real.exp |η| :=
      Real.pow_div_factorial_le_exp |η| (abs_nonneg η) (2 * k)
    have s3' : |η| ^ (2 * k) ≤ (Nat.factorial (2 * k) : ℝ) * Real.exp |η| := by
      have h := (div_le_iff₀ hFpos).mp s3
      linarith
    have s4 : Real.exp |η| ≤ 2 * Real.cosh η := by
      rw [Real.cosh_eq]
      have h := Real.exp_abs_le η
      linarith
    have s4' : (Nat.factorial (2 * k) : ℝ) * Real.exp |η|
        ≤ (Nat.factorial (2 * k) : ℝ) * (2 * Real.cosh η) :=
      mul_le_mul_of_nonneg_left s4 hFpos.le
    have hcosh : (1 : ℝ) ≤ Real.cosh η := Real.one_le_cosh η
    -- Step 5: `1 + |η|^(2k) ≤ (1 + 2 (2k)!) cosh η`.
    have s5 : 1 + (η ^ 2) ^ k
        ≤ (1 + 2 * (Nat.factorial (2 * k) : ℝ)) * Real.cosh η := by
      rw [hpow]
      nlinarith [s3', s4', hcosh]
    calc (1 + η ^ 2) ^ N
        ≤ (1 + η ^ 2) ^ k := s1
      _ ≤ (2 : ℝ) ^ (k - 1) * (1 + (η ^ 2) ^ k) := s2
      _ ≤ (2 : ℝ) ^ (k - 1) * ((1 + 2 * (Nat.factorial (2 * k) : ℝ)) * Real.cosh η) :=
          mul_le_mul_of_nonneg_left s5 (by positivity)
      _ = (2 : ℝ) ^ (k - 1) * (1 + 2 * (Nat.factorial (2 * k) : ℝ)) * Real.cosh η := by ring

end CylPDE

end UnforcedLeray.Short.IIb
