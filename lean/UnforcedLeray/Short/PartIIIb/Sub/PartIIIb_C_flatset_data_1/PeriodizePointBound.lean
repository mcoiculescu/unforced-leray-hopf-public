import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Linear weight against the exponential: `1 + ρ ≤ (1 + 16A) e^{ρ/(16A)}` for `ρ ≥ 0`. -/
theorem pb_lin_le_exp (A ρ : ℝ) (hA : 0 < A) (hρ : 0 ≤ ρ) :
    1 + ρ ≤ (1 + 16 * A) * Real.exp (ρ / (16 * A)) := by
  have h16 : (16 * A) ≠ 0 := (by linarith : (0:ℝ) < 16 * A).ne'
  have ht0 : 0 ≤ ρ / (16 * A) := div_nonneg hρ (by linarith)
  have e := Real.add_one_le_exp (ρ / (16 * A))
  have hk : 16 * A * (ρ / (16 * A)) = ρ := by
    field_simp
  have hpos : 0 ≤ (1 + 16 * A) := by linarith
  nlinarith [mul_nonneg hpos (by linarith : (0:ℝ) ≤ Real.exp (ρ / (16 * A)) - (ρ / (16 * A) + 1))]

/-- Gaussian weight comparison: `(1+ρ)² e^{-ρ/(4A)} ≤ (1+16A)² e^{-ρ/(8A)}` for `ρ ≥ 0`. -/
theorem pb_weight_le (A ρ : ℝ) (hA : 0 < A) (hρ : 0 ≤ ρ) :
    (1 + ρ) ^ 2 * Real.exp (-ρ / (4 * A)) ≤ (1 + 16 * A) ^ 2 * Real.exp (-ρ / (8 * A)) := by
  have h1 := pb_lin_le_exp A ρ hA hρ
  have h2 : (1 + ρ) * (1 + ρ) ≤ ((1 + 16 * A) * Real.exp (ρ / (16 * A))) *
      ((1 + 16 * A) * Real.exp (ρ / (16 * A))) :=
    mul_le_mul h1 h1 (by linarith) (mul_nonneg (by linarith) (Real.exp_pos _).le)
  have h3 : Real.exp (ρ / (16 * A)) * Real.exp (ρ / (16 * A)) * Real.exp (-ρ / (4 * A))
      = Real.exp (-ρ / (8 * A)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hE : 0 ≤ Real.exp (-ρ / (4 * A)) := (Real.exp_pos _).le
  have h4 : (1 + ρ) ^ 2 * Real.exp (-ρ / (4 * A)) ≤
      ((1 + 16 * A) * Real.exp (ρ / (16 * A))) ^ 2 * Real.exp (-ρ / (4 * A)) := by
    apply mul_le_mul_of_nonneg_right _ hE
    nlinarith [h2]
  calc (1 + ρ) ^ 2 * Real.exp (-ρ / (4 * A))
      ≤ ((1 + 16 * A) * Real.exp (ρ / (16 * A))) ^ 2 * Real.exp (-ρ / (4 * A)) := h4
    _ = (1 + 16 * A) ^ 2 * (Real.exp (ρ / (16 * A)) * Real.exp (ρ / (16 * A)) *
          Real.exp (-ρ / (4 * A))) := by ring
    _ = (1 + 16 * A) ^ 2 * Real.exp (-ρ / (8 * A)) := by rw [h3]

/-- The tail inequality for the periodic images: for `|x₁| ≤ c/2`,
`x₁²/2 + n²c²/8 ≤ (x₁ - nc)²` for every `n ∈ ℤ`. -/
theorem pb_tail (x1 c : ℝ) (n : ℤ) (hc : 0 < c) (hx : |x1| ≤ c / 2) :
    x1 ^ 2 / 2 + (n : ℝ) ^ 2 * c ^ 2 / 8 ≤ (x1 - (n : ℝ) * c) ^ 2 := by
  obtain ⟨hl, hr⟩ := abs_le.mp hx
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hm : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hnc : (n : ℝ) * c ≤ -c := by nlinarith
    have hF1 : x1 ^ 2 ≤ (x1 - (n : ℝ) * c) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -((n : ℝ) * c))
        (by linarith : (0:ℝ) ≤ -((n : ℝ) * c) + 2 * x1)]
    have hF2 : (n : ℝ) ^ 2 * c ^ 2 / 4 ≤ (x1 - (n : ℝ) * c) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -(3 * ((n : ℝ) * c) / 2 - x1))
        (by linarith : (0:ℝ) ≤ -(((n : ℝ) * c) / 2 - x1))]
    nlinarith [hF1, hF2]
  · subst hn
    norm_num <;> nlinarith [sq_nonneg x1]
  · have hm : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hnc : c ≤ (n : ℝ) * c := by nlinarith
    have hF1 : x1 ^ 2 ≤ (x1 - (n : ℝ) * c) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (n : ℝ) * c)
        (by linarith : (0:ℝ) ≤ (n : ℝ) * c - 2 * x1)]
    have hF2 : (n : ℝ) ^ 2 * c ^ 2 / 4 ≤ (x1 - (n : ℝ) * c) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * ((n : ℝ) * c) / 2 - x1)
        (by linarith : (0:ℝ) ≤ ((n : ℝ) * c) / 2 - x1)]
    nlinarith [hF1, hF2]

/-- Exponent comparison of the periodic images on the cell, uniformly in `c ≥ c₀`. -/
theorem pb_expbound (A c0 c x1 x2 : ℝ) (n : ℤ) (hA : 0 < A) (hc0 : 0 < c0) (hcc : c0 ≤ c)
    (hx : |x1| ≤ c / 2) :
    Real.exp (-((x1 - (n : ℝ) * c) ^ 2 + x2 ^ 2) / (8 * A)) ≤
      Real.exp (-(x1 ^ 2 + x2 ^ 2) / (16 * A)) *
        Real.exp (-((c0 ^ 2 / (64 * A)) * (n : ℝ) ^ 2)) := by
  have hc : 0 < c := lt_of_lt_of_le hc0 hcc
  have ht := pb_tail x1 c n hc hx
  have hc2 : c0 ^ 2 ≤ c ^ 2 := by nlinarith [mul_le_mul hcc hcc hc0.le hc.le]
  have hn2 : (n : ℝ) ^ 2 * c0 ^ 2 ≤ (n : ℝ) ^ 2 * c ^ 2 :=
    mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)
  have hX : (x1 ^ 2 / 2 + (n : ℝ) ^ 2 * c0 ^ 2 / 8 + x2 ^ 2) / (8 * A) ≤
      ((x1 - (n : ℝ) * c) ^ 2 + x2 ^ 2) / (8 * A) := by
    gcongr
    linarith
  have hY : (x1 ^ 2 / 2 + (n : ℝ) ^ 2 * c0 ^ 2 / 8 + x2 ^ 2) / (8 * A) =
      x1 ^ 2 / (16 * A) + (c0 ^ 2 / (64 * A)) * (n : ℝ) ^ 2 + x2 ^ 2 / (8 * A) := by
    ring
  have hZ : x2 ^ 2 / (16 * A) ≤ x2 ^ 2 / (8 * A) := by
    gcongr
    linarith
  have e1 : -((x1 - (n : ℝ) * c) ^ 2 + x2 ^ 2) / (8 * A) =
      -(((x1 - (n : ℝ) * c) ^ 2 + x2 ^ 2) / (8 * A)) := neg_div _ _
  have e2 : -(x1 ^ 2 + x2 ^ 2) / (16 * A) = -(x1 ^ 2 / (16 * A)) - x2 ^ 2 / (16 * A) := by
    ring
  have hexp : -((x1 - (n : ℝ) * c) ^ 2 + x2 ^ 2) / (8 * A) ≤
      -(x1 ^ 2 + x2 ^ 2) / (16 * A) + -((c0 ^ 2 / (64 * A)) * (n : ℝ) ^ 2) := by
    rw [e1, e2]
    linarith [hX, hY, hZ]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 hexp

/-- Summability of the lattice Gaussian `n ↦ e^{-B n²}` over `ℤ` for `B > 0`. -/
theorem pb_summable (B : ℝ) (hB : 0 < B) :
    Summable (fun n : ℤ => Real.exp (-(B * (n : ℝ) ^ 2))) := by
  have hr : Real.exp (-B) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hr0 : 0 ≤ Real.exp (-B) := (Real.exp_pos _).le
  have hnat : Summable (fun n : ℕ => Real.exp (-(B * ((n : ℤ) : ℝ) ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (summable_geometric_of_lt_one hr0 hr)
    rw [Int.cast_natCast, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have h1 : 1 ≤ n := h
        have : (1 : ℝ) ≤ n := by exact_mod_cast h1
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hn hB.le]
  refine Summable.of_nat_of_neg hnat ?_
  refine hnat.congr fun n => ?_
  push_cast
  ring_nf

/-- **Pointwise Gaussian bound of the periodization on the cell, uniformly in `c ≥ c₀`**
(source 4565-4574: the images are at distance `≥ c/2`). -/
theorem periodizePointBound : PeriodizePointBound := by
  intro A c₀ hA hc₀
  have hB : 0 < c₀ ^ 2 / (64 * A) := div_pos (pow_pos hc₀ 2) (by linarith)
  have hsum := pb_summable (c₀ ^ 2 / (64 * A)) hB
  refine ⟨(1 + 16 * A) ^ 2 * ∑' n : ℤ, Real.exp (-((c₀ ^ 2 / (64 * A)) * (n : ℝ) ^ 2)),
    fun c hc g K hg x hx => ?_⟩
  have hc0 : 0 < c := lt_of_lt_of_le hc₀ hc
  -- the sign of `K`, from the bound at the point `x`
  have hK : 0 ≤ K := by
    have h0 := hg x
    have hP : 0 < (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := by
      apply mul_pos (by positivity) (Real.exp_pos _)
    by_contra hneg
    push_neg at hneg
    nlinarith [norm_nonneg (g x), mul_neg_of_neg_of_pos hneg hP]
  -- the term bound
  have hterm : ∀ n : ℤ, ‖g (x.1 - (n : ℝ) * c, x.2)‖ ≤
      K * (1 + 16 * A) ^ 2 * (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)) *
        Real.exp (-((c₀ ^ 2 / (64 * A)) * (n : ℝ) ^ 2))) := by
    intro n
    have h1 : ‖g (x.1 - (n : ℝ) * c, x.2)‖ ≤
        K * (1 + ((x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2)) ^ 2 *
          Real.exp (-((x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2) / (4 * A)) := by
      have h := hg (x.1 - (n : ℝ) * c, x.2)
      have hform : (1 + (x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2) =
          1 + ((x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2) := by ring
      rw [hform] at h
      exact h
    have hk := pb_weight_le A ((x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2) hA (by positivity)
    have hexpb := pb_expbound A c₀ c x.1 x.2 n hA hc₀ hc hx
    calc ‖g (x.1 - (n : ℝ) * c, x.2)‖
        ≤ K * (1 + ((x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2)) ^ 2 *
          Real.exp (-((x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2) / (4 * A)) := h1
      _ = K * ((1 + ((x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2)) ^ 2 *
          Real.exp (-((x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2) / (4 * A))) := by ring
      _ ≤ K * ((1 + 16 * A) ^ 2 * Real.exp (-((x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2) / (8 * A))) :=
          mul_le_mul_of_nonneg_left hk hK
      _ ≤ K * ((1 + 16 * A) ^ 2 * (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)) *
          Real.exp (-((c₀ ^ 2 / (64 * A)) * (n : ℝ) ^ 2)))) := by
          apply mul_le_mul_of_nonneg_left _ hK
          exact mul_le_mul_of_nonneg_left hexpb (by positivity)
      _ = K * (1 + 16 * A) ^ 2 * (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)) *
          Real.exp (-((c₀ ^ 2 / (64 * A)) * (n : ℝ) ^ 2))) := by ring
  have hsumbd : Summable (fun n : ℤ => K * (1 + 16 * A) ^ 2 *
      (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)) *
        Real.exp (-((c₀ ^ 2 / (64 * A)) * (n : ℝ) ^ 2)))) :=
    (hsum.mul_left (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)))).mul_left (K * (1 + 16 * A) ^ 2)
  have hnorm : Summable (fun n : ℤ => ‖g (x.1 - (n : ℝ) * c, x.2)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsumbd
  have hperiod : IIIa.periodizeC c g x = ∑' n : ℤ, g (x.1 - (n : ℝ) * c, x.2) := rfl
  rw [hperiod]
  calc ‖∑' n : ℤ, g (x.1 - (n : ℝ) * c, x.2)‖
      ≤ ∑' n : ℤ, ‖g (x.1 - (n : ℝ) * c, x.2)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℤ, K * (1 + 16 * A) ^ 2 *
          (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)) *
            Real.exp (-((c₀ ^ 2 / (64 * A)) * (n : ℝ) ^ 2))) :=
          Summable.tsum_le_tsum hterm hnorm hsumbd
    _ = K * (1 + 16 * A) ^ 2 * (Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)) *
          ∑' n : ℤ, Real.exp (-((c₀ ^ 2 / (64 * A)) * (n : ℝ) ^ 2))) := by
          rw [tsum_mul_left, tsum_mul_left]
    _ = (1 + 16 * A) ^ 2 * (∑' n : ℤ, Real.exp (-((c₀ ^ 2 / (64 * A)) * (n : ℝ) ^ 2))) * K *
          Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * A)) := by
          ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
