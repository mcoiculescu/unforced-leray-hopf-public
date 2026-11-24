import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Units.B0147
import UnforcedLeray.Units.B0146
import UnforcedLeray.Units.B0579
import Mathlib.Analysis.Complex.Exponential

/-!
# Part III-a, `PartIII-a:T21/2/6/9`: weighted lattice sums on the centred cell

Source of record: `the November 2 reference manuscript`, lines 2866-2867, 3044.
For `|g(y)| ≤ K e^{-β|y|²}` and `L ≥ 1`, the periodized sum `Σₙ g(y - nL e₁)` satisfies
`⟨y⟩^{2k} |Σₙ g(y - nL e₁)| ≤ C` on the centred cell `C_L = [-L/2, L/2) × ℝ`, where `(y₁-nL)² ≥ y₁²`
for every integer `n`, so the lattice sum is dominated by `e^{-(β/2)y₁²}` times the one-dimensional
lattice sum with `β/2`, and `⟨y⟩^{2k} e^{-(β/2)(⟨y⟩²-1)} ≤ k!(2/β)^k e^{β/2}`.

Statement: `CenteredLatticeWeighted`.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Pointwise: on the centred cell, `y₁² ≤ (y₁ - nL)²` for every integer `n` (`L ≥ 1`). -/
theorem centered_key {L : ℝ} (hL : 1 ≤ L) {y1 : ℝ} (h1 : -(L / 2) ≤ y1) (h2 : y1 < L / 2)
    (n : ℤ) : y1 ^ 2 ≤ (y1 - n * L) ^ 2 := by
  obtain h | h | h : n = 0 ∨ 1 ≤ n ∨ n ≤ -1 := by omega
  · subst h; simp
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast h
    have hA : (0 : ℝ) ≤ (n : ℝ) * L - 2 * y1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) (by linarith : (0 : ℝ) ≤ L)]
    have hB : (0 : ℝ) ≤ (n : ℝ) * L := by nlinarith
    nlinarith [mul_nonneg hB hA]
  · have hn : (n : ℝ) ≤ -1 := by exact_mod_cast h
    have hB : (n : ℝ) * L ≤ 0 := by nlinarith
    have hA : (n : ℝ) * L - 2 * y1 ≤ 0 := by nlinarith
    nlinarith [mul_nonneg (neg_nonneg.mpr hB) (neg_nonneg.mpr hA)]

/-- `(1 + t)^k e^{-(β/2)t} ≤ k!(2/β)^k e^{β/2}` for `t ≥ 0`, `β > 0`. -/
theorem centered_pow_exp_le (k : ℕ) {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ k * Real.exp (-((β / 2) * t)) ≤
      ((k.factorial : ℝ) * (2 / β) ^ k) * Real.exp (β / 2) := by
  set x : ℝ := (β / 2) * (1 + t) with hxdef
  have hx : 0 ≤ x := mul_nonneg (by linarith) (by linarith)
  have h1 : x ^ k / (k.factorial : ℝ) ≤ Real.exp x := Real.pow_div_factorial_le_exp x hx k
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : x ^ k ≤ (k.factorial : ℝ) * Real.exp x := by
    have h3 := (div_le_iff₀ hfac).mp h1
    linarith [mul_comm (Real.exp x) (k.factorial : ℝ)]
  have h3 : x ^ k = (β / 2) ^ k * (1 + t) ^ k := by rw [hxdef, mul_pow]
  have hc : (2 / β) ^ k * (β / 2) ^ k = 1 := by
    rw [← mul_pow]
    have : (2 / β) * (β / 2) = 1 := by field_simp
    rw [this, one_pow]
  have h4 : (1 + t) ^ k ≤ ((k.factorial : ℝ) * (2 / β) ^ k) * Real.exp x := by
    calc (1 + t) ^ k = (2 / β) ^ k * ((β / 2) ^ k * (1 + t) ^ k) := by
          rw [← mul_assoc, hc, one_mul]
      _ ≤ (2 / β) ^ k * ((k.factorial : ℝ) * Real.exp x) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← h3]; exact h2
      _ = ((k.factorial : ℝ) * (2 / β) ^ k) * Real.exp x := by ring
  have hexp : Real.exp x * Real.exp (-((β / 2) * t)) = Real.exp (β / 2) := by
    rw [← Real.exp_add]
    congr 1
    rw [hxdef]; ring
  calc (1 + t) ^ k * Real.exp (-((β / 2) * t))
      ≤ (((k.factorial : ℝ) * (2 / β) ^ k) * Real.exp x) * Real.exp (-((β / 2) * t)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
    _ = ((k.factorial : ℝ) * (2 / β) ^ k) * (Real.exp x * Real.exp (-((β / 2) * t))) := by ring
    _ = ((k.factorial : ℝ) * (2 / β) ^ k) * Real.exp (β / 2) := by rw [hexp]

theorem centeredLatticeWeighted : CenteredLatticeWeighted := by
  intro K β hK hβ k
  have hθ : 0 ≤ UnforcedLeray.B0147.theta (β / 16) := UnforcedLeray.B0147.theta_nonneg _
  refine ⟨K * (2 + UnforcedLeray.B0147.theta (β / 16)) *
    ((k.factorial : ℝ) * (2 / β) ^ k) * Real.exp (β / 2), ?_⟩
  intro g hg L hL y hy
  have hL0 : L ≠ 0 := by intro h; rw [h] at hL; norm_num at hL
  have hy1 : y.1 ∈ Set.Ico (-(L / 2)) (L / 2) := (Set.mem_prod.mp hy).1
  obtain ⟨hy1a, hy1b⟩ := Set.mem_Ico.mp hy1
  have key := centered_key hL hy1a hy1b
  -- the lattice sum is dominated by a one-dimensional Gaussian lattice sum
  have hbound := UnforcedLeray.B0147.latticeSum_abs_le hK hβ hL0 hg y
  have hs1 := UnforcedLeray.B0146.summable_exp_shift hβ hL0 y.1
  have hs2 := (UnforcedLeray.B0146.summable_exp_shift (by linarith : (0 : ℝ) < β / 2) hL0 y.1).mul_left
    (Real.exp (-((β / 2) * y.1 ^ 2)))
  have hpt : ∀ n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2)) ≤
      Real.exp (-((β / 2) * y.1 ^ 2)) * Real.exp (-((β / 2) * (y.1 - n * L) ^ 2)) := by
    intro n
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [key n, mul_nonneg hβ.le (sub_nonneg.mpr (key n))]
  have hsum_le : ∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2)) ≤
      Real.exp (-((β / 2) * y.1 ^ 2)) * (2 + UnforcedLeray.B0147.theta (β / 16)) := by
    calc ∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2))
        ≤ ∑' n : ℤ, Real.exp (-((β / 2) * y.1 ^ 2)) * Real.exp (-((β / 2) * (y.1 - n * L) ^ 2)) :=
          hs1.tsum_le_tsum hpt hs2
      _ = Real.exp (-((β / 2) * y.1 ^ 2)) *
            ∑' n : ℤ, Real.exp (-((β / 2) * (y.1 - n * L) ^ 2)) := tsum_mul_left
      _ ≤ Real.exp (-((β / 2) * y.1 ^ 2)) * (2 + UnforcedLeray.B0147.theta (β / 16)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          have h := UnforcedLeray.B0147.lattice1D_sup (by linarith : (0 : ℝ) < β / 2) hL y.1
          rw [show (β / 2) / 8 = β / 16 by ring] at h
          exact h
  -- combine the factors into one Gaussian in `|y|²`
  have hcomb : Real.exp (-(β * y.2 ^ 2)) * Real.exp (-((β / 2) * y.1 ^ 2)) ≤
      Real.exp (-((β / 2) * (y.1 ^ 2 + y.2 ^ 2))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hβ.le (sq_nonneg y.2)]
  have hstep : |UnforcedLeray.B0146.latticeSum L g y| ≤
      (K * (2 + UnforcedLeray.B0147.theta (β / 16))) *
        Real.exp (-((β / 2) * (y.1 ^ 2 + y.2 ^ 2))) := by
    refine hbound.trans ?_
    have hK' : 0 ≤ K * Real.exp (-(β * y.2 ^ 2)) := mul_nonneg hK (Real.exp_nonneg _)
    calc K * Real.exp (-(β * y.2 ^ 2)) * ∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2))
        ≤ K * Real.exp (-(β * y.2 ^ 2)) *
            (Real.exp (-((β / 2) * y.1 ^ 2)) * (2 + UnforcedLeray.B0147.theta (β / 16))) :=
          mul_le_mul_of_nonneg_left hsum_le hK'
      _ = (K * (2 + UnforcedLeray.B0147.theta (β / 16))) *
            (Real.exp (-(β * y.2 ^ 2)) * Real.exp (-((β / 2) * y.1 ^ 2))) := by ring
      _ ≤ (K * (2 + UnforcedLeray.B0147.theta (β / 16))) *
            Real.exp (-((β / 2) * (y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left hcomb (mul_nonneg hK (by linarith))
  -- the weight `⟨y⟩^{2k}` against the Gaussian
  have hjb : UnforcedLeray.B0579.jb y = 1 + (y.1 ^ 2 + y.2 ^ 2) := by
    unfold UnforcedLeray.B0579.jb; ring
  rw [hjb]
  have hpow := centered_pow_exp_le k hβ (by positivity : (0 : ℝ) ≤ y.1 ^ 2 + y.2 ^ 2)
  calc (1 + (y.1 ^ 2 + y.2 ^ 2)) ^ k * |UnforcedLeray.B0146.latticeSum L g y|
      ≤ (1 + (y.1 ^ 2 + y.2 ^ 2)) ^ k *
          ((K * (2 + UnforcedLeray.B0147.theta (β / 16))) *
            Real.exp (-((β / 2) * (y.1 ^ 2 + y.2 ^ 2)))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (K * (2 + UnforcedLeray.B0147.theta (β / 16))) *
          ((1 + (y.1 ^ 2 + y.2 ^ 2)) ^ k *
            Real.exp (-((β / 2) * (y.1 ^ 2 + y.2 ^ 2)))) := by ring
    _ ≤ (K * (2 + UnforcedLeray.B0147.theta (β / 16))) *
          (((k.factorial : ℝ) * (2 / β) ^ k) * Real.exp (β / 2)) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hK (by linarith))
    _ = K * (2 + UnforcedLeray.B0147.theta (β / 16)) *
          ((k.factorial : ℝ) * (2 / β) ^ k) * Real.exp (β / 2) := by ring

end UnforcedLeray.Short.IIIa
